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

package net.sourceforge.czt.animation.gui.design.properties.editors;

import java.beans.BeanDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyEditorSupport;
import java.util.HashMap;
import java.util.Map;

import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;

/**
 * <code>PropertyEditor</code> for <code>TableModel</code>s.
 * Used in the property editing window for editing <code>TableModel</code>
 * properties.
 */
public class TableModelEditor extends PropertyEditorSupport
{
  private static final Map<String, Class<?>> tableModelClasses =
    new HashMap<String, Class<?>>();

  public static void registerTableModel(Class<?> c)
  {
    if (c.isInterface() || !TableModel.class.isAssignableFrom(c))
      throw new IllegalArgumentException("Classes registered with "
          + "TableModelEditor must represent " + "classes that implement "
          + "javax.swing.table.TableModel");
    try {
      BeanDescriptor bd = Introspector.getBeanInfo(c).getBeanDescriptor();
      tableModelClasses.put(bd.getName(), c);
    } catch (IntrospectionException ex) {
      tableModelClasses.put(c.getName(), c);
    }
  };

  public String getAsText()
  {
    Class<?> valueClass = getValue().getClass();
    try {
      BeanDescriptor bd = Introspector.getBeanInfo(valueClass)
          .getBeanDescriptor();
      return bd.getName();
    } catch (IntrospectionException ex) {
      return valueClass.getName();
    }
  };

  public void setAsText(String className)
  {
    try {
      setValue(((Class<?>) tableModelClasses.get(className)).newInstance());
    } catch (Exception ex) {
      setValue(new DefaultTableModel());
    }
  };

  public String[] getTags()
  {
    return (String[]) tableModelClasses.keySet().toArray(new String[0]);
  };
};
