package czt.animation.gui.design.properties;

import java.beans.BeanInfo;
import java.beans.Introspector;
import java.beans.IntrospectionException;

import javax.swing.event.TableModelEvent;

import javax.swing.table.AbstractTableModel;

/**
 * The table model of events that a bean provides that appears in the properties window.
 * @see czt.animation.gui.design.properties.PropertiesWindow
 */
class EventsTable extends AbstractTableModel {
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
   * Creates an events table without specifying a bean to look at.
   */
  public EventsTable() {
    this(null);
  };
  /**
   * Creates an events table looking at the events of <code>bean</code>.
   */
  public EventsTable(Object bean) {
    setBean(bean);
  };
  
  /**
   * Returns the number of rows in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getRowCount() {
    if(beanInfo==null) return 0;
    return beanInfo.getEventSetDescriptors().length;
  };
  /**
   * Returns the number of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public int getColumnCount() {
    return 2;
  };
  /**
   * Returns the name of columns in this table.  Inherited from <code>AbstractTableModel</code>.
   */
  public String getColumnName(int column) {
    switch(column) {
     case 0: return "Event name";
     case 1: return "Listener type";
    }return "ERROR";
  };
  /**
   * Returns the value stored in each cell of this table. 
   * Inherited from <code>AbstractTableModel</code>.
   */
  public Object getValueAt(int row, int column) {
    switch(column) {
     case 0: return beanInfo.getEventSetDescriptors()[row].getDisplayName();
     case 1: return beanInfo.getEventSetDescriptors()[row].getListenerType().getName();
    }return "ERROR";  
  };
};
