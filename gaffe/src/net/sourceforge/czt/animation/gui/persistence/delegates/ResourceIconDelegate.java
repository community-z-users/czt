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

import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;

import net.sourceforge.czt.animation.gui.beans.ResourceIcon;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * Persistence delegate for
 * {@link net.sourceforge.czt.animation.gui.beans.ResourceIcon ResourceIcon}s.
 * @see "java.xml.Encoder"
 */
public final class ResourceIconDelegate extends DefaultPersistenceDelegate
{
  /**
   * The singleton instance.
   */
  private static final ResourceIconDelegate SINGLETON = new ResourceIconDelegate();

  /**
   * Block construction.  This class follows the singleton patttern, so we don't
   * want people instantiating it.
   * @see "Erich Gamma, Richard Helm, Ralph Johnson, and John Vlissides. Design
   *       Patterns: Elements of Reusable Object-Oriented Software. Addison
   *       Wesley, USA, 1995."
   */
  private ResourceIconDelegate()
  {
  };

  /**
   * Registers the persistence delegate so that it will be used.
   */
  public static void registerDelegate()
  {
    try {
      final BeanInfo beanInfo = Introspector.getBeanInfo(ResourceIcon.class);
      IntrospectionHelper.rememberBeanInfo(beanInfo);
      beanInfo.getBeanDescriptor().setValue("persistenceDelegate", SINGLETON);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining "
          + "ResourceIcon from ResourceIconDelegate." + ex);
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
    return newInstance != null;
  };

  /**
   * Return an expression whose value is oldInstance.
   * @param oldInstance The instance that will be created by the expression.
   * @param out The <code>Encoder</code> it will be written to.
   */
  protected Expression instantiate(Object oldInstance, Encoder out)
  {
    ResourceIcon oldIcon = (ResourceIcon) oldInstance;
    return new Expression(oldIcon, ResourceIcon.class, "new",
        new Object[]{oldIcon.getURL()});
  };
};
