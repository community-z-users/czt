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

import czt.animation.gui.history.History;
import czt.animation.gui.history.BasicHistory;

import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextProxy;
import java.beans.beancontext.BeanContextServices;
import java.beans.beancontext.BeanContextServicesSupport;

import java.io.FileNotFoundException;

import javax.swing.JFileChooser;
import javax.swing.JOptionPane;

/**
 * The base for AnimatorCore and AnimatorScrollingCore
 */
abstract class AnimatorCoreBase implements BeanContextProxy {
  //Properties:
  /**
   * History property.
   * Keeps track of history of solution sets.
   */
  protected History history;
  /**
   * Getter function for {@link #history history}.
   * @return The property <code>history</code>.
   * @see #history
   */
  public History    getHistory()                  {return history;};
  /**
   * Setter function for {@link #history history}.
   * @param h The property <code>history</code>.
   * @see #history
   */
  public void       setHistory(History h)         {history=h;};
  
  //BeanContextProxy stuff
  /**
   * The Bean context for this object (proxied through 
   * {@link #getBeanContextProxy() #getBeanContextProxy()}).
   * Provides services to contexts and beans in the program.
   */
  protected BeanContextServices    rootContext;
  /**
   * Getter function for {@link #rootContext rootContext}.
   * @return The root context.
   * @see #rootContext
   * @see java.beans.beancontext.BeanContextProxy
   */
  public BeanContextChild getBeanContextProxy() {return rootContext;};
  
  //Constructors
  /**
   * Default constructor.
   * Sets history to be a {@link czt.animation.gui.history.BasicHistory BasicHistory}.
   * Sets to design mode.
   * Initialises empty context.
   * @see czt.animation.gui.history.BasicHistory
   */
  protected AnimatorCoreBase() {
    this(new BasicHistory(),new BeanContextServicesSupport());
  };

  /**
   * Constructor.
   * Allows subclasses to override the defaults for {@link #history history}, 
   * and {@link #rootContext rootContext}.
   * @param h history
   * @param rc rootContext
   */
  protected AnimatorCoreBase(History h, BeanContextServices rc) {
    history=h; 
    rootContext=rc;
  };

  /**
   * Constructor.
   * Allows subclasses to override the defaults for {@link #history history}, 
   * and {@link #rootContext rootContext}.
   * @param h history
   */
  protected AnimatorCoreBase(History h) {
    this(h,new BeanContextServicesSupport());
  };

  public static int run(String[] args) {
    JFileChooser fc=new JFileChooser();
    while(fc.showOpenDialog(null)!=JFileChooser.APPROVE_OPTION);

    try {
      new AnimatorCore(fc.getSelectedFile());
    } catch (FileNotFoundException ex) {
      JOptionPane.showMessageDialog(null,"Couldn't open file","File not found",
				    JOptionPane.ERROR_MESSAGE);
    };
  
  
    
    return 0;//XXX choose between AnimatorCore styles.
  };
  
};
