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

import java.beans.BeanInfo;
import java.beans.Introspector;
import java.beans.IntrospectionException;
import java.beans.MethodDescriptor;

import java.lang.reflect.Method;

import java.util.Iterator;
import java.util.Vector;

import javax.swing.event.TableModelEvent;

import javax.swing.table.AbstractTableModel;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The table model of methods that a bean provides that appears in the properties window.
 * @see net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow
 */
class MethodsTable extends AbstractTableModel {
   /**
   * The bean that this table is for.
   */ 
  protected Object bean;
  /**
   * The bean info for <code>bean</code>'s class.
   */
  protected BeanInfo beanInfo;

  protected final Vector/*<MethodDescriptor>*/ methodDescriptors=new Vector();  

  public final void setMethodDescriptors() {
    methodDescriptors.clear();
    if(beanInfo==null) return;
    MethodDescriptor[] descriptors=beanInfo.getMethodDescriptors();
    for(int i=0;i<descriptors.length;i++) {
      if((    propertiesWindow.getHiddenShown()        ||!descriptors[i].isHidden())
	 && ( propertiesWindow.getExpertShown()        ||!descriptors[i].isExpert())
	 && (!propertiesWindow.getOnlyPreferredShown() || descriptors[i].isPreferred())
	 && ( propertiesWindow.getTransientShown()     ||!Boolean.TRUE.equals(descriptors[i]
									      .getValue("transient"))))
	methodDescriptors.add(descriptors[i]);
    } 
     
    fireTableChanged(new TableModelEvent(this));
    fireTableStructureChanged();
  }
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
    setMethodDescriptors();
  };
  
  /**
   * Creates a methods table without specifying a bean to look at.
   */
  public MethodsTable(PropertiesWindow window) {
    this(null,window);
  };

  protected PropertiesWindow propertiesWindow;
  
  /**
   * Creates a methods table looking at the methods of <code>bean</code>.
   */
  public MethodsTable(Object bean,PropertiesWindow window) {
    setBean(bean);
    propertiesWindow=window;
  };
  
  /**
   * Returns the number of rows in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getRowCount() {
    return methodDescriptors.size();
  };
  /**
   * Returns the number of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getColumnCount() {
    int max=0;
    if(beanInfo==null) return 1;
    for(Iterator it=methodDescriptors.iterator();it.hasNext();)
      max=Math.max(max,((MethodDescriptor)it.next()).getMethod().getParameterTypes().length);
    return 1+max;
  };
  /**
   * Returns the name of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public String getColumnName(int column) {
    switch(column) {
     case 0:return "Method name";
     default:return "arg "+column;
    }
  };
  /**
   * Returns the value stored in each cell of this table. 
   * Inherited from <code>AbstractTableModel</code>.
   */
  public Object getValueAt(int row, int column) {
    MethodDescriptor md=(MethodDescriptor)methodDescriptors.get(row);
    switch(column) {
     case 0:return md.getDisplayName();
     default:
       Method m=md.getMethod();
       if(m==null) return "?";
       if (m.getParameterTypes().length<column) return "";
       return IntrospectionHelper.translateClassName(m.getParameterTypes()[column-1]);
    }
  };
};
