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
package czt.animation.gui;

import com.ibm.bsf.BSFManager;

import czt.animation.gui.history.History;
import czt.animation.gui.scripting.BSFServiceProvider;

import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;

import java.beans.XMLDecoder;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import java.util.Vector;

import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JOptionPane;

/**
 * The core program for normal animation of a specification.
 */
class AnimatorCore extends AnimatorCoreBase {
  /**
   * Creates an AnimatorCore.
   */
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

  private final Vector/*<Form>*/ forms=new Vector();
  
  public AnimatorCore(File file) throws FileNotFoundException{
    //    super(new FakeHistory());
    XMLDecoder decoder;
    decoder=new XMLDecoder(new FileInputStream(file));

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
	frame.setVisible(newForm.isVisible());
	
	newForm.setLocation(0,0);
	newForm.setPreferredSize(newForm.getSize());
	frame.getContentPane().add(newForm);
	frame.setSize(frame.getPreferredSize());
	forms.add(frame);
	decoder.readObject();//beanWrappers
	decoder.readObject();//eventLinks
	rootContext.add(newForm);
	//XXX attach the event links properly.
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
    };
    
    //XXX Load Z specification.
    //XXX Display appropriate forms.
    
    BSFManager bsfm=new BSFManager();
    //XXX (register any new scripting languages)
    //XXX register and declare beans in bsfm
    bsfm.registerBean("History",history);
    bsfm.registerBean("AnimatorCore",this);
    bsfm.registerBean("Forms",forms);

    rootContext.addService(BSFManager.class,new BSFServiceProvider(bsfm));
    
  };
  
};
