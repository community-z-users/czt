package czt.animation.gui.design.properties;

import java.beans.BeanInfo;
import java.beans.Introspector;
import java.beans.IntrospectionException;
import java.beans.MethodDescriptor;

import java.lang.reflect.Method;

import javax.swing.event.TableModelEvent;

import javax.swing.table.AbstractTableModel;

/**
 * The table model of methods that a bean provides that appears in the properties window.
 * @see czt.animation.gui.design.properties.PropertiesWindow
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
    
    fireTableChanged(new TableModelEvent(this));
    fireTableStructureChanged();
  };
  
  /**
   * Creates a methods table without specifying a bean to look at.
   */
  public MethodsTable() {
    this(null);
  };
  /**
   * Creates a methods table looking at the methods of <code>bean</code>.
   */
  public MethodsTable(Object bean) {
    setBean(bean);
  };
  
  /**
   * Returns the number of rows in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getRowCount() {
    if(beanInfo==null) return 0;
      
    return beanInfo.getMethodDescriptors().length;
  };
  /**
   * Returns the number of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getColumnCount() {
    int max=0;
    if(beanInfo==null) return 1;
    for(int row=0;row<beanInfo.getMethodDescriptors().length;row++)
      max=Math.max(max,beanInfo.getMethodDescriptors()[row].getMethod().getParameterTypes().length);
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
    MethodDescriptor md=beanInfo.getMethodDescriptors()[row];
    switch(column) {
     case 0:return md.getDisplayName();
     default:
       Method m=md.getMethod();
       if(m==null) return "?";
       if (m.getParameterTypes().length<column) return "";
       return m.getParameterTypes()[column-1].getName();
    }
  };
};
