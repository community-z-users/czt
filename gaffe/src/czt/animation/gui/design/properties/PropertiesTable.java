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
package czt.animation.gui.design.properties;

import czt.animation.gui.util.IntrospectionHelper;

import java.awt.Component;

import java.awt.event.ActionEvent;        import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;          import java.awt.event.ItemListener;

import java.beans.BeanInfo;               import java.beans.IntrospectionException;
import java.beans.Introspector;           import java.beans.PropertyEditor;
import java.beans.PropertyEditorManager;

import java.util.Vector;

import javax.swing.JComboBox;             import javax.swing.JOptionPane;
import javax.swing.JTextField;

import javax.swing.event.TableModelEvent;

import javax.swing.table.AbstractTableModel; import javax.swing.table.TableCellEditor;

/**
 * The table model of properties that a bean provides that appears in the properties window.
 * @see czt.animation.gui.design.properties.PropertiesWindow
 */
class PropertiesTable extends AbstractTableModel {
  PropertiesTable() {
    setBean(null);
  };
  

  /**
   * The bean that this table is for.
   */
  protected Object bean;
  /**
   * The bean info for <code>bean</code>'s class.
   */
  protected BeanInfo beanInfo;
  /**
   * Getter function for bean.
   */
  public Object getBean() {
    return bean;
  }
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
    editorComponents=new Vector();
    editorComponents.setSize(getRowCount()+1);
    propertyEditors=new Vector();
    propertyEditors.setSize(getRowCount()+1);
    fireTableChanged(new TableModelEvent(this));
    fireTableStructureChanged();
  };

  /**
   * Returns the number of rows in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getRowCount() {
    if(beanInfo==null) return 0;
    return beanInfo.getPropertyDescriptors().length;
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
  public Class getTypeAt(int row) {
    return beanInfo.getPropertyDescriptors()[row].getPropertyType();
  };

  protected Object getObject(int row) {
    return IntrospectionHelper.getBeanProperty(bean,beanInfo.getPropertyDescriptors()[row].getName());
  };
  
  /**
   * Returns the value stored in each cell of this table. 
   * Inherited from <code>AbstractTableModel</code>.
   */
  public Object getValueAt(int row, int column) {
//      System.err.println("###");
//      System.err.println(beanInfo.getPropertyDescriptors()[row].getDisplayName());
//      if(beanInfo.getPropertyDescriptors()[row].getPropertyType()!=null) {
//        System.err.println(beanInfo.getPropertyDescriptors()[row].getPropertyType().getName());
//      }
//      System.err.println(IntrospectionHelper
//  		       .beanHasWritableProperty(bean,beanInfo.getPropertyDescriptors()[row]
//  						.getDisplayName()));
      
    switch(column) {
     case 0: return beanInfo.getPropertyDescriptors()[row].getDisplayName();
     case 1:
       if(getTypeAt(row)==null) {
	 return "((Indexed))";
       };//XXX should change all places where using Class.getName() to translate the result
       return getTypeAt(row).getName();
     case 2: 
       if(getTypeAt(row)==null) {
	 return "((Indexed))";
       };
       return getObject(row);
    }
    return "ERROR";
  };
  /**
   * Returns true if a particular cell is editable.  Inherited from <code>AbstractTableModel</code>.
   */
  public boolean isCellEditable(int row, int column) {
    System.err.println("!!!!!!!!Checki