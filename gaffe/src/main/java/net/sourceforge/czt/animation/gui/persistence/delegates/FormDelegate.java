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

package net.sourceforge.czt.animation.gui.persistence.delegates;

import java.awt.Component;
import java.awt.Container;
import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.Statement;
import java.beans.beancontext.BeanContext;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.animation.gui.Form;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * Persistence delegate for
 * {@link net.sourceforge.czt.animation.gui.Form Form}s.
 * @see "java.xml.Encoder"
 */
public final class FormDelegate extends DefaultPersistenceDelegate
{
  /**
   * The singleton instance.
   */
  private static final FormDelegate SINGLETON = new FormDelegate();

  /**
   * Block construction.  This class follows the singleton patttern, so we don't
   * want people instantiating it.
   * @see "Erich Gamma, Richard Helm, Ralph Johnson, and John Vlissides. Design
   *       Patterns: Elements of Reusable Object-Oriented Software. Addison
   *       Wesley, USA, 1995."
   */
  private FormDelegate()
  {
  };

  /**
   * Registers the persistence delegate so that it will be used.
   */
  public static void registerDelegate()
  {
    try {
      final BeanInfo beanInfo = Introspector.getBeanInfo(Form.class);
      IntrospectionHelper.rememberBeanInfo(beanInfo);
      beanInfo.getBeanDescriptor().setValue("persistenceDelegate", SINGLETON);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining Form "
          + "from FormDelegate." + ex);
    }
  };

  /**
   * Returns true if an equivalent copy of <code>oldInstance</code> can be made
   * from <code>newInstance</code>.
   * @param oldInstance The instance to be copied.
   * @param newInstance The instance to be modified.
   */
  protected boolean mutatesTo(Object oldInstance, Object newInstance)
  {
    if (newInstance == null) {
      return false;
    }

    Form f = (Form) newInstance;
    BeanContext bc = (BeanContext) f.getBeanContextProxy();
    if (bc.size() == 0) {
      return true;
    }
    return false;
  };

  /**
   * Produces statements on <code>newInstance</code> so that
   * <code>newInstance</code> becomes equivalent to <code>oldInstance</code>.
   * @param type XXX
   * @param oldInstance The instance to be copied.
   * @param newInstance The instance to be modified.
   * @param out The encoder to write the statements to.
   */
  protected void initialize(Class<?> type, Object oldInstance, Object newInstance,
      Encoder out)
  {
    Form oldForm = (Form) oldInstance;
    Form newForm = (Form) newInstance;
    //BeanContext oldBeanContext = (BeanContext) oldForm.getBeanContextProxy();
    //BeanContext newBeanContext = (BeanContext) newForm.getBeanContextProxy();

    //The location for the form bean should be transient, however location
    //doesn't seem to appear as a property for components, and XMLEncoder seems
    //to ignore the transient property on x and y.
    //So we'll make it look like the location is the default, so it won't get
    //stored.
    newForm.setLocation(oldForm.getLocation());
    //There are similar problems with listeners, which are handled by
    //DesignerCore's XMLEncoder's overriden writeStatement.

    Form f = (Form) oldInstance;

    for (Iterator<?> i = ((BeanContext) f.getBeanContextProxy()).iterator(); i
        .hasNext();) {
      Object obj = i.next();
      if (!(obj instanceof Component))
        out.writeStatement(new Statement(oldInstance, "addBean",
            new Object[]{obj}));
    }
    super.initialize(type, oldInstance, newInstance, out);
  };

  /**
   * Used to sort the list of beans in a form based on the order they appear in
   * their parents.
   * @param c the container whose children are recursively added to newList
   * @param bc only beans in this list are added to newList, after they are
   *   added to newList, they are removed from bc.
   * @param newList the list the beans are added to.
   * @return newList.
   */
  protected static List<Component> makeSortedComponentList(Container c, 
		  	List<Component> bc, List<Component> newList)
  {
    Component[] components = c.getComponents();
    for (int i = 0; i < components.length; i++)
      if (!newList.contains(components[i]) && bc.contains(components[i])) {
        bc.remove(components[i]);
        newList.add(components[i]);
        if (components[i] instanceof Container)
          makeSortedComponentList((Container) components[i], bc, newList);
      }
    return newList;
  };
};
