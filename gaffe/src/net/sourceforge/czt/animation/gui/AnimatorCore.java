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

import java.beans.XMLDecoder;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JOptionPane;

import net.sourceforge.czt.animation.gui.design.BeanLink;

import net.sourceforge.czt.animation.gui.history.History;
import net.sourceforge.czt.animation.gui.history.HistoryServiceProvider;

import net.sourceforge.czt.animation.gui.scripting.BSFServiceProvider;

import net.sourceforge.czt.animation.gui.temp.*;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The core program for normal animation of a specification.
 */
public class AnimatorCore extends AnimatorCoreBase {
  /**
   * Creates an AnimatorCore.
   */
  protected String initScript="";
  protected String initScriptLanguage="javascript";
  public void setInitScript(String initScript) {this.initScript=initScript;};
  public void setInitScriptLanguage(String initScriptLanguage) {this.initScriptLanguage=initScriptLanguage;};
  public String getInitScript() {return initScript;};
  public String getInitScriptLanguage() {return initScriptLanguage;};
  

//    public AnimatorCore() {
//      JFileChooser fc=new JFileChooser();
//      if(fc.showOpenDialog(null)!=JFileChooser.APPROVE_OPTION) 
//        return;
//      try {
//        this(fc.getSelectedFile());
//      } catch (FileNotFoundException ex) {
//        JOptionPane.showMessageDialog(null,"Couldn't open file","File not found",
//  				    JOptionPane.ERROR_MESSAGE);
//      };
//    };
  
  
  public AnimatorCore(String fileName) throws FileNotFoundException{
    this(new File(fileName));
  };

  private final Vector/*<Form>*/ forms=new Vector() {
      public Form lookup(String name) {//For use by scripts.
	for(Iterator it=iterator();it.hasNext();) {
	  Form f=(Form)it.next();
	  if(f.getName().equals(name)) return f;
	}
	return null;
      };
    };
  
  public AnimatorCore(File file) throws FileNotFoundException{
    super(new BirthdayBookHistory());
    XMLDecoder decoder;
    decoder=new XMLDecoder(new FileInputStream(file), this);

    try {
      while(true) {
	final Form newForm;
	newForm=(Form)decoder.readObject();
	final JFrame frame=new JFrame() {
	    public void setVisible(boolean b) {
	      super.setVisible(b);
	      if(newForm.isVisible()!=b) newForm.setVisible(b);
	    };
	  };
	newForm.addComponentListener(new ComponentAdapter() {
	    public void componentShown(ComponentEvent e) {
	      frame.setVisible(true);
	    };
	    public void componentHidden(ComponentEvent e) {
	      frame.setVisible(false);
	    };
	  });
	if(!newForm.isPreferredSizeSet()) newForm.setPreferredSize(newForm.getSize());
	
	newForm.setLocation(0,0);
	frame.getContentPane().setLayout(new BorderLayout());
	frame.getContentPane().add(newForm,BorderLayout.CENTER);
	frame.pack();
	frame.setVisible(newForm.isVisible());
	forms.add(newForm);
	decoder.readObject();//beanWrappers
	Vector beanLinks=(Vector)decoder.readObject();//eventLinks
	for(Iterator iter=beanLinks.iterator();iter.hasNext();) {
	  BeanLink bl=(BeanLink)iter.next();
	  IntrospectionHelper.addBeanListener(bl.source,bl.listenerType,bl.listener);
	}
	rootContext.add(newForm);
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
    };
    
    //XXX Load Z specification.
    //XXX Display appropriate forms.
    
    BSFManager bsfm=new BSFManager();
    //XXX (register any new scripting languages)
    //XXX register and declare beans in bsfm
    try {
      bsfm.declareBean("History",history,history.getClass());
      bsfm.declareBean("AnimatorCore",this,this.getClass());
      bsfm.declareBean("Forms",forms,forms.getClass());
      bsfm.declareBean("err",System.err,System.err.getClass());
      bsfm.declareBean("out",System.out,System.out.getClass());
    } catch (BSFException ex) {
      throw new Error("History,AnimatorCore, or Forms couldn't be declared with the Scripting Engine. "
		      +ex);
    }
    
    rootContext.addService(BSFManager.class,new BSFServiceProvider(bsfm));
    rootContext.addService(History.class,new HistoryServiceProvider(history));
    try {
      bsfm.exec(initScriptLanguage,"init",1,1,initScript);
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
  };
};

