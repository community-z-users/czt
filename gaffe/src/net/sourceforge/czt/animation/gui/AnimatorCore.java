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

import com.ibm.bsf.BSFException;
import com.ibm.bsf.BSFManager;

import java.awt.BorderLayout;

import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.XMLDecoder;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import java.net.MalformedURLException;
import java.net.URL;

import java.util.Iterator;
import java.util.Vector;

import javax.swing.JFrame;

import net.sourceforge.czt.animation.gui.design.BeanLink;

import net.sourceforge.czt.animation.gui.history.History;
import net.sourceforge.czt.animation.gui.history.HistoryServiceProvider;

import net.sourceforge.czt.animation.gui.scripting.BSFServiceProvider;

import net.sourceforge.czt.animation.gui.temp.*;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The core program for normal animation of a specification.
 */
public class AnimatorCore extends AnimatorCoreBase
{
  /**
   * Creates an AnimatorCore.
   */
  protected String initScript_ = "";
  protected String initScriptLanguage_ = "javascript";
  protected URL specificationURL_ = null;

  private final Vector/*<Form>*/ forms_ = new Vector() {
    public Form lookup(String name)
    { //For use by scripts.
      for (Iterator it = iterator(); it.hasNext();) {
        Form f = (Form) it.next();
        if (f.getName().equals(name)) return f;
      }
      return null;
    };
  };

  public AnimatorCore(String fileName)
    throws FileNotFoundException
  {
    this(new File(fileName));
  };

  public AnimatorCore(File file)
    throws FileNotFoundException
  {
    super(new BirthdayBookHistory());
    XMLDecoder decoder;
    decoder = new XMLDecoder(new FileInputStream(file), this);

    try {
      while (true) {
        final Form newForm;
        newForm = (Form) decoder.readObject();
        final JFrame frame = new JFrame() {
          public void setVisible(boolean b)
          {
            super.setVisible(b);
            if (newForm.isVisible() != b) newForm.setVisible(b);
          };
        };

        newForm.addComponentListener(new ComponentAdapter() {
          public void componentHidden(ComponentEvent e)
          {
            //If the last form was closed, then quit.
            Vector visibleForms = new Vector(forms_);
            for (Iterator i = visibleForms.iterator(); i.hasNext();)
              if (!((Form) i.next()).isVisible()) i.remove();
            visibleForms.remove(e.getComponent());
            if (visibleForms.isEmpty())
              System.exit(0);
          };
        });
        newForm.addPropertyChangeListener("title",
                                          new PropertyChangeListener() {
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
        Vector beanLinks = (Vector) decoder.readObject(); //eventLinks
        for (Iterator iter = beanLinks.iterator(); iter.hasNext();) {
          BeanLink bl = (BeanLink) iter.next();
          IntrospectionHelper.addBeanListener(bl.source, bl.listenerType,
                                              bl.listener);
        }
        rootContext.add(newForm);
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
    };

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
    for(Iterator it=forms_.iterator();it.hasNext();) {
      Form form=(Form)it.next();
      boolean v=form.getStartsVisible();
      form.setVisible(v);
      System.err.println("Setting visible "+form.getName()+" = "+v);
    }
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
};

