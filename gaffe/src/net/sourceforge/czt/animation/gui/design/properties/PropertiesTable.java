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
package net.sourceforge.czt.animation.gui.design.properties;

import java.beans.BeanInfo;               import java.beans.IntrospectionException;
import java.beans.Introspector;           import java.beans.PropertyDescriptor;     

import java.util.Vector;

import javax.swing.event.TableModelEvent;

import javax.swing.table.AbstractTableModel;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The table model of properties that a bean provides that appears in the properties window.
 * @see net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow
 */
final class PropertiesTable extends AbstractTableModel {

  public PropertiesTable(PropertiesWindow window) {
    setBean(null);
    propertiesWindow=window;
  };
  
  private PropertiesWindow propertiesWindow;
  
  /**
   * The bean that this table is for.
   */
  private Object bean;
  /**
   * The bean info for <code>bean</code>'s class.
   */
  private BeanInfo beanInfo;
  
  private final Vector/*<PropertyDescriptor>*/ propertyDescriptors=new Vector();  
  
  public final void setPropertyDescriptors() {
    propertyDescriptors.clear();
    if(beanInfo==null) return;
    PropertyDescriptor[] descriptors=beanInfo.getPropertyDescriptors();
    for(int i=0;i<descriptors.length;i++) {
      if((    propertiesWindow.getHiddenShown()        ||!descriptors[i].isHidden())
	 && ( propertiesWindow.getExpertShown()        ||!descriptors[i].isExpert())
	 && (!propertiesWindow.getOnlyPreferredShown() || descriptors[i].isPreferred())
	 && ( propertiesWindow.getTransientShown()     ||!Boolean.TRUE.equals(descriptors[i]
									      .getValue("transient")))
	 && (!propertiesWindow.getOnlyEditableShown()  || isCellEditable(descriptors[i]))) {
	propertyDescriptors.add(descriptors[i]);
      }
    }
    fireTableChanged(new TableModelEvent(this));
    fireTableStructureChanged();  
  };
  
  public final PropertyDescriptor getPropertyDescriptor(int row) {
    return (PropertyDescriptor)propertyDescriptors.get(row);
  };
  
  /** 
   * Setter function for bean.
   */
  public void setBean(Object bean) {
    this.bean=bean;
    beanInfo=null;
    if(bean!=null) try {
      beanInfo=Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
	System.err.println("COULDN'T GET BeanInfo");
	System.err.println(e);
    };
    setPropertyDescriptors();
  };

  /**
   * Returns the number of rows in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getRowCount() {
    return propertyDescriptors.size();
  };
    

  public Class getColumnClass(int columnIndex) {
    return (columnIndex==2)?Object.class:String.class;
  };

  /**
   * Returns the number of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getColumnCount() {
    return 3;
  };
  /**
   * Returns the name of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public String getColumnName(int column) {
    switch(column) {
     case 0: return "Property name";
     case 1: return "Type";
     case 2: return "Value";
    }
    return "ERROR";
  };
  private Class getTypeAt(int row) {
    return ((PropertyDescriptor)propertyDescriptors.get(row)).getPropertyType();
  };

  private Object getObject(int row) {
    return IntrospectionHelper.getBeanProperty(bean,(PropertyDescriptor)propertyDescriptors.get(row));
  };
  
  /**
   * Returns the value stored in each cell of this table. 
   * Inherited from <code>AbstractTableModel</code>.
   */
  public Object getValueAt(int row, int column) {
      
    switch(column) {
     case 0: return ((PropertyDescriptor)propertyDescriptors.get(row)).getDisplayName();
     case 1:
       if(getTypeAt(row)==null) {
	 return "((Indexed))";
       };//XXX should change all places where using Class.getName() to translate the result
       return IntrospectionHelper.translateClassName(getTypeAt(row));
     case 2: 
       if(getTypeAt(row)==null) {
	 return "((Indexed))";
       };
       return getObject(row);
    }
    return "ERROR";
  };

  private boolean isCellEditable(PropertyDescriptor pd) {
    return IntrospectionHelper.isWritableProperty(pd)
      && IntrospectionHelper.getEditor(pd.getPropertyType())!=null;
  };
  
  /**
   * Returns true if a particular cell is editable.  Inherited from <code>AbstractTableModel</code>.
   */
  public boolean isCellEditable(int row, int column) {
    return column==2 
      && (propertiesWindow.getOnlyEditableShown() //This check unnecessary, but saves time on the next check.
	  || isCellEditable((PropertyDescriptor)propertyDescriptors.get(row)));
  };
  /**
   * Sets the value of the item in a particular cell.  Inherited from <code>AbstractTableModel</code>.
   */
  public void setValueAt(Object value, int row, int column) {
    //XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXx
    //XXX Needs to change to fit in with stopCellEditing in PropertiesWindow.java
    //    Need to figure out what to do about custom editors.
    //XXX Commented out because at present, this is handled in the PropertyCellEditor class
  };
};
