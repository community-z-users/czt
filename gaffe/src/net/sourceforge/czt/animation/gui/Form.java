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

import net.sourceforge.czt.animation.gui.persistence.delegates.FormDelegate;

import java.awt.Component;

import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextProxy;
import java.beans.beancontext.BeanContextServicesSupport;

import java.util.EventListener;

import javax.swing.JPanel;
import javax.swing.event.EventListenerList;

/**
 * A Form constitutes a designable panel, window, or dialog.  Forms are designed by a
 * {@link net.sourceforge.czt.animation.gui.design.FormDesign FormDesign} object.
 */
public class Form extends JPanel implements BeanContextProxy {
  /**
   * Support class for Bean Context Services.  This is used to
   * <ul>
   *   <li>associate non-Component beans with the form,</li>
   *   <li>provide access to the BSF scripting engine to beans.</li>
   * </ul>
   */
  protected BeanContextServicesSupport bcsSupport=new BeanContextServicesSupport();

  /**
   * Support class for keeping track of listeners.  Especially used for the <code>FormListener</code>s.
   * @see net.sourceforge.czt.animation.gui.FormEvent
   * @see net.sourceforge.czt.animation.gui.FormListener
   */
  protected EventListenerList listenerSupport=new EventListenerList();
  
  /**
   * Creates a Form without a name.
   */
  public Form() {
    this(null);
  };
  /**
   * Creates a Form with a name.
   */
  public Form(String name) {
    super(null);
    setName(name);
    bcsSupport.addService(Form.class, new FormServiceProvider(this));
  };
  /**
   * Allows access to the BeanContext contained in this class.
   * Inherited from BeanContextProxy.
   */
  public BeanContextChild getBeanContextProxy() {
    return bcsSupport;
  };
  
  /**
   * Adds a bean to the form.  Triggers a <code>FormEvent</code> going to the <code>beanAdded</code>
   * function of a listener.
   */
  public void addBean(Object bean) {
    if(bean instanceof Component)
      add((Component)bean);
    bcsSupport.add(bean);
    FormListener[] listeners=(FormListener[])getListeners(FormListener.class);
    
    for(int i=0;i<listeners.length;i++)
      listeners[i].beanAdded(new FormEvent(this,bean,FormEvent.ADDED));
  };

  public boolean removeBean(Object bean) {
    if(!bcsSupport.contains(bean)) return false;
    if(bean instanceof Component) {
      remove((Component)bean);
    };
    bcsSupport.remove(bean);
    FormListener[] listeners=(FormListener[])getListeners(FormListener.class);
    
    for(int i=0;i<listeners.length;i++)
      listeners[i].beanRemoved(new FormEvent(this,bean,FormEvent.REMOVED));
    return true;
  }
  
  public Object[] getBeans() {
    return bcsSupport.toArray();
  };
  
  /**
   * Adds a listener for <code>FormEvent</code>.
   */
  public void addFormListener(FormListener l) {
    listenerSupport.add(FormListener.class,l);
  };
  /**
   * Removes a listener for <code>FormEvent</code>.
   */
  public void removeFormListener(FormListener l) {
    listenerSupport.remove(FormListener.class,l);
  };
  /**
   * Returns all of the listeners of class <code>c</code>.
   */
  public EventListener[] getListeners(Class c) {
    return listenerSupport.getListeners(c);
  };

  static {
    FormDelegate.registerDelegate();
  };
  
};
//XXX add function removeBean
