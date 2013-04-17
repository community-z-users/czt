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

import java.awt.Component;
import java.awt.Container;
import java.awt.event.ContainerEvent;
import java.awt.event.ContainerListener;
import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextProxy;
import java.beans.beancontext.BeanContextServicesSupport;
import java.util.EventListener;
import java.util.Iterator;

import javax.swing.JPanel;
import javax.swing.JScrollPane;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * A Form constitutes a designable panel, window, or dialog.  Forms are
 * designed by a
 * {@link net.sourceforge.czt.animation.gui.design.FormDesign FormDesign}
 * object.
 */
public class Form extends JPanel implements BeanContextProxy
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 1064438787206256259L;

/**
   * Support class for Bean Context Services.  This is used to
   * <ul>
   *   <li>associate non-Component beans with the form,</li>
   *   <li>provide access to the BSF scripting engine to beans.</li>
   * </ul>
   */
  protected BeanContextServicesSupport bcsSupport = new BeanContextServicesSupport();

  /**
   * Title property - ends up in title bar of Frame.
   */
  private String title = "";

  /**
   * StartsVisible property - true if this form should be open when the animator
   * starts up.
   */
  private boolean startsVisible = false;

  /**
   * Creates a Form without a name.
   */
  public Form()
  {
    this(null);
  };

  /**
   * Creates a Form with a name.
   */
  public Form(String name)
  {
    super(null);
    setName(name);
    setTitle(name);
    bcsSupport.addService(Form.class, new FormServiceProvider(this));
    addContainerListener(new ContainerListener()
    {
      private void addBean(Object bean)
      {
        if (bcsSupport.contains(bean))
          return;
        bcsSupport.add(bean);
        fireFormEvent(new FormEvent(Form.this, bean, FormEvent.ADDED));
        if (bean instanceof Container) {
          Container beanAsContainer = (Container) bean;
          beanAsContainer.addContainerListener(this);
          Component[] children = beanAsContainer.getComponents();
          for (int i = 0; i < children.length; i++)
            addBean(children[i]);
        }
      };

      public void componentAdded(ContainerEvent e)
      {
        addBean(e.getChild());
      };

      private void removeBean(Object bean)
      {
        if (!bcsSupport.contains(bean))
          return;

        if (bean instanceof Container) {
          Container beanAsContainer = (Container) bean;
          beanAsContainer.removeContainerListener(this);
          Component[] children = beanAsContainer.getComponents();
          for (int i = 0; i < children.length; i++)
            removeBean(children[i]);
        }
        bcsSupport.remove(bean);
        fireFormEvent(new FormEvent(Form.this, bean, FormEvent.REMOVED));
      };

      public void componentRemoved(ContainerEvent e)
      {
        removeBean(e.getChild());
      };
    });
  };

  private void fireFormEvent(FormEvent ev)
  {
    FormListener[] listeners = getFormListeners();
    for (int i = 0; i < listeners.length; i++)
      listeners[i].beanAdded(ev);
  };

  /**
   * Allows access to the BeanContext contained in this class.
   * Inherited from BeanContextProxy.
   */
  public BeanContextChild getBeanContextProxy()
  {
    return bcsSupport;
  };

  /**
   * Adds a bean to the form.  Triggers a <code>FormEvent</code> going to the
   * <code>beanAdded</code> function of a listener.
   */
  public void addBean(Object bean)
  {
    if (bean instanceof Component)
      addBean((Component) bean, this);
    else {
      bcsSupport.add(bean);
      FormListener[] listeners = getFormListeners();
      for (int i = 0; i < listeners.length; i++)
        listeners[i].beanAdded(new FormEvent(this, bean, FormEvent.ADDED));
    }
  };

  public void addBean(Component bean, Container parent)
  {
    if (parent instanceof JScrollPane)
      ((JScrollPane) parent).getViewport().setView(bean);
    else
      parent.add(bean);
    //bcsSupport.add(bean);
    //FormListener[] listeners=getFormListeners();

    //for (int i=0;i<listeners.length;i++)
    //listeners[i].beanAdded(new FormEvent(this,bean,FormEvent.ADDED));
  };

  public boolean removeBean(Object bean)
  {
    if (!bcsSupport.contains(bean))
      return false;
    if (bean instanceof Container) {
      Component[] comps = ((Container) bean).getComponents();
      for (int i = 0; i < comps.length; i++)
        removeBean(comps[i]);
    };
    if (bean instanceof Component) {
      ((Component) bean).getParent().remove((Component) bean);
    };
    bcsSupport.remove(bean);
    FormListener[] listeners = getFormListeners();

    for (int i = 0; i < listeners.length; i++)
      listeners[i].beanRemoved(new FormEvent(this, bean, FormEvent.REMOVED));
    return true;
  }

  public Object[] getBeans()
  {
    return bcsSupport.toArray();
  };

  public Object lookup(String string)
  {
    for (Iterator<?> it = bcsSupport.iterator(); it.hasNext();) {
      Object bean = it.next();
      if (string.equals(IntrospectionHelper.getBeanProperty(bean, "name")))
        return bean;
    }
    return null;
  };

  /**
   * Adds a listener for <code>FormEvent</code>.
   */
  public void addFormListener(FormListener l)
  {
    listenerList.add(FormListener.class, l);
  };

  /**
   * Removes a listener for <code>FormEvent</code>.
   */
  public void removeFormListener(FormListener l)
  {
    listenerList.remove(FormListener.class, l);
  };

  /**
   * Returns all of the listeners of class <code>c</code>.
   */
  public <T extends EventListener> T[] getListeners(Class<T> c)
  {
    return listenerList.getListeners(c);
  };

  /**
   * Returns all of the <code>FormListener</code>s.
   */
  public FormListener[] getFormListeners()
  {
    return (FormListener[]) listenerList.getListeners(FormListener.class);
  };

  /**
   * Getter method for <code>title</code>.
   */
  public String getTitle()
  {
    return title;
  };

  /**
   * Setter method for <code>title</code>.
   */
  public void setTitle(String title)
  {
    String oldTitle = this.title;
    this.title = title;
    firePropertyChange("title", oldTitle, title);
  };

  /**
   * Getter method for <code>startsVisible</code>.
   */
  public boolean getStartsVisible()
  {
    return startsVisible;
  };

  /**
   * Setter method for <code>startsVisible</code>.
   */
  public void setStartsVisible(boolean startsVisible)
  {
    boolean oldStartsVisible = this.startsVisible;
    this.startsVisible = startsVisible;
    firePropertyChange("startsVisible", oldStartsVisible, startsVisible);
  };

  /**
   * Overridden to tie the form's visibility with that of the window containing
   * it.
   */
  public void setVisible(boolean visible)
  {
    super.setVisible(visible);
    Container window = getTopLevelAncestor();
    if (window != null)
      window.setVisible(visible);
  };
};
