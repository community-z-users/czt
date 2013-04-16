/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui;

import java.awt.BorderLayout;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.beans.Beans;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.XMLDecoder;
import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextServices;
import java.beans.beancontext.BeanContextServicesSupport;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Iterator;
import java.util.Vector;

import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JOptionPane;

import net.sourceforge.czt.animation.gui.design.BeanLink;
import net.sourceforge.czt.animation.gui.history.History;
import net.sourceforge.czt.animation.gui.history.HistoryServiceProvider;
import net.sourceforge.czt.animation.gui.history.ZLiveHistory;
import net.sourceforge.czt.animation.gui.scripting.BSFServiceProvider;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;
import net.sourceforge.czt.animation.gui.util.Utils;

import org.apache.bsf.BSFException;
import org.apache.bsf.BSFManager;

/**
 * The core program for normal animation of a specification.
 */
public class AnimatorCore
{
  //Properties:

  /**
   * History property.
   * Keeps track of history of solution sets.
   */
  protected History history;

  /**
   * The Bean context for this object (proxied through
   * {@link #getBeanContextProxy() #getBeanContextProxy()}).
   * Provides services to contexts and beans in the program.
   */
  protected BeanContextServices rootContext;

  protected String initScript_ = "";

  protected String initScriptLanguage_ = "javascript";

  protected URL specificationURL_ = null;

  private final Vector<Form> forms_ = new Vector<Form>()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -5956597780794486110L;

	@SuppressWarnings("unused")
	public Form lookup(String name)
    { //For use by scripts.
      for (Iterator<Form> it = iterator(); it.hasNext();) {
        Form f = it.next();
        if (f.getName().equals(name))
          return f;
      }
      return null;
    };
  };

  public AnimatorCore(String fileName) throws FileNotFoundException
  {
    this(new File(fileName));
  };

  @SuppressWarnings("unchecked")
public AnimatorCore(File file) throws FileNotFoundException
  {
    Beans.setDesignTime(false);
    rootContext = new BeanContextServicesSupport();
    try{
      URL specURL = new URL("file:///E:/czt/zml/examples/z/birthdaybook_unfolded.tex");
      history = new ZLiveHistory("BirthdayBook","InitBirthdayBook",specURL);
    }
    catch (MalformedURLException ex){
      ex.printStackTrace();
    }
    

    XMLDecoder decoder;
    decoder = new XMLDecoder(new FileInputStream(file), this);

    try {
      while (true) {
        final Form newForm;
        newForm = (Form) decoder.readObject();
        final JFrame frame = new JFrame()
        {
          /**
			 * 
			 */
			private static final long serialVersionUID = 4731706062562233200L;

		public void setVisible(boolean b)
          {
            super.setVisible(b);
            if (newForm.isVisible() != b)
              newForm.setVisible(b);
          };
        };

        newForm.addComponentListener(new ComponentAdapter()
        {
          public void componentHidden(ComponentEvent e)
          {
            //If the last form was closed, then quit.
            Vector<Form> visibleForms = new Vector<Form>(forms_);
            for (Iterator<Form> i = visibleForms.iterator(); i.hasNext();)
              if (!i.next().isVisible())
                i.remove();
            visibleForms.remove(e.getComponent());
            if (visibleForms.isEmpty())
              System.exit(0);
          };
        });
        newForm.addPropertyChangeListener("title", new PropertyChangeListener()
        {
          public void propertyChange(PropertyChangeEvent evt)
          {
            frame.setTitle((String) evt.getNewValue());
          };
        });

        if (!newForm.isPreferredSizeSet())
          newForm.setPreferredSize(newForm.getSize());

        newForm.setLocation(0, 0);
        frame.getContentPane().setLayout(new BorderLayout());
        frame.getContentPane().add(newForm, BorderLayout.CENTER);
        frame.pack();
        frame.setTitle(newForm.getTitle());

        //XXX URGENT setVisible should be moved after the init scripts.
        //    If somebody starts using the interface before the init script 
        //    finishes it can have `weird and fun' side-effects
        //        frame.setVisible(newForm.getStartsVisible());

        forms_.add(newForm);
        decoder.readObject(); //beanWrappers
        // unchecked
		Vector<BeanLink> beanLinks = (Vector<BeanLink>) decoder.readObject(); //eventLinks
        for (Iterator<BeanLink> iter = beanLinks.iterator(); iter.hasNext();) {
          BeanLink bl = iter.next();
          IntrospectionHelper.addBeanListener(bl.source, bl.listenerType,
              bl.listener);
        }
        rootContext.add(newForm); // unchecked
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
    } finally {
      decoder.close();
    }

    //XXX Load Z specification.
    //XXX Display appropriate forms.

    BSFManager bsfm = new BSFManager();
    //XXX (register any new scripting languages)
    //XXX register and declare beans in bsfm
    try {
      bsfm.declareBean("History", history, history.getClass());
      bsfm.declareBean("AnimatorCore", this, this.getClass());
      bsfm.declareBean("Forms", forms_, forms_.getClass());
      bsfm.declareBean("err", System.err, System.err.getClass());
      bsfm.declareBean("out", System.out, System.out.getClass());
    } catch (BSFException ex) {
      throw new Error("History,AnimatorCore, or Forms couldn't be declared "
          + "with the Scripting Engine. " + ex);
    }

    rootContext.addService(BSFManager.class, new BSFServiceProvider(bsfm));
    rootContext.addService(History.class, new HistoryServiceProvider(history));
    try {
      bsfm.exec(initScriptLanguage_, "init", 1, 1, initScript_);
    } catch (BSFException ex) {
      //XXX Do something?
      //error dialog?
      //send message back?
      //make it settable?
      System.err.println("Init Script caught BSFException:");
      System.err.println(ex);
      ex.printStackTrace();
      System.err.println("------");
      ex.getTargetException().printStackTrace();
    };
    for (Iterator<Form> it = forms_.iterator(); it.hasNext();) {
      Form form =  it.next();
      boolean v = form.getStartsVisible();
      form.setVisible(v);
      System.err.println("Setting visible " + form.getName() + " = " + v);
    }
  };

  /**
   * Getter function for {@link #history history}.
   * @return The property <code>history</code>.
   * @see #history
   */
  public History getHistory()
  {
    return history;
  };

  /**
   * Setter function for {@link #history history}.
   * @param h The property <code>history</code>.
   * @see #history
   */
  public void setHistory(History h)
  {
    history = h;
  };

  //BeanContextProxy stuff
  /**
   * Getter function for {@link #rootContext rootContext}.
   * @return The root context.
   * @see #rootContext
   * @see java.beans.beancontext.BeanContextProxy
   */
  public BeanContextChild getBeanContextProxy()
  {
    return rootContext;
  };

  public void setInitScript(String initScript)
  {
    initScript_ = initScript;
  };

  public void setInitScriptLanguage(String initScriptLanguage)
  {
    initScriptLanguage_ = initScriptLanguage;
  };

  public String getInitScript()
  {
    return initScript_;
  };

  public String getInitScriptLanguage()
  {
    return initScriptLanguage_;
  };

  public void setSpecificationURL(String specificationURL)
  {
    try {
      specificationURL_ = new URL(specificationURL);
    } catch (MalformedURLException ex) {
      specificationURL_ = null;
    };
  };

  public String getSpecificationURL()
  {
    return specificationURL_.toExternalForm();
  };

  public static int run(String[] args)
  {
    File file = null;
    if (args.length == 0) {
      JFileChooser fc = new JFileChooser();
      fc.addChoosableFileFilter(Utils.gaffeFileFilter);

      if (fc.showOpenDialog(null) != JFileChooser.APPROVE_OPTION)
        return -1;
      file = fc.getSelectedFile();
    }
    else
      file = new File(args[0]);

    try {
      new AnimatorCore(file);
    } catch (FileNotFoundException ex) {
      JOptionPane.showMessageDialog(null, "Couldn't open file",
          "File not found", JOptionPane.ERROR_MESSAGE);
    };
    return 0;
  };
};
