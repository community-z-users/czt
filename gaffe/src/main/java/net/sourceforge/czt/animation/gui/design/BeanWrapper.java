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

package net.sourceforge.czt.animation.gui.design;

import java.awt.Color;
import java.awt.Component;
import java.beans.BeanDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import javax.swing.BorderFactory;
import javax.swing.JLabel;

/**
 * Class to wrap around non-visual beans so that they have a visual
 * representation in the FormDesign.
 * Appears as a label with the bean's class name as its text.
 * @see net.sourceforge.czt.animation.gui.design.FormDesign
 */
public class BeanWrapper extends JLabel
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 1362402089586584567L;
/**
   * The bean this object wraps around.
   */
  protected Object bean;

  /**
   * Creates a bean wrapper without specifying the bean to wrap.
   */
  public BeanWrapper()
  {
    this(null);
  };

  /**
   * Creates a bean wrapper around <code>b</code>.
   */
  public BeanWrapper(Object b)
  {
    setBean(b);
    setBorder(BorderFactory.createLineBorder(Color.black));
    setSize(getPreferredSize());
  };

  /**
   * Getter function for bean.
   */
  public Object getBean()
  {
    return bean;
  };

  /**
   * Setter function for bean.
   */
  public void setBean(Object b)
  {
    wrappers.remove(bean);
    wrappers.put(b, new WeakReference<BeanWrapper>(this));
    bean = b;
    if (b == null) {
      setText("(null)");
      return;
    }
    Class<?> beanClass = b.getClass();
    try { //XXX show name property? listener to catch name changes?
      BeanDescriptor bd = Introspector.getBeanInfo(beanClass)
          .getBeanDescriptor();
      setText(bd.getDisplayName());
      setToolTipText(bd.getShortDescription());
    } catch (IntrospectionException e) {
      setText(beanClass.getName());
    };
  };

  public static Object getBean(Component c)
  {
    if (c == null)
      return null;
    else if (c instanceof BeanWrapper)
      return ((BeanWrapper) c).getBean();
    else
      return c;
  };

  private static WeakHashMap<Object, WeakReference<BeanWrapper>> wrappers = new WeakHashMap<Object, WeakReference<BeanWrapper>>();

  public static Component getComponent(Object b)
  {
    if (b == null)
      return null;
    else if (b instanceof Component)
      return (Component) b;
    WeakReference<BeanWrapper> r =wrappers.get(b);
    BeanWrapper w = null;
    if (r != null)
      w = (BeanWrapper) r.get();
    if (w == null)
      w = new BeanWrapper(b);
    return w;
  };
};
