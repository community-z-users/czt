package czt.animation.gui.design.properties;

import java.awt.*;
import java.beans.*;
import java.lang.reflect.Method;
import java.util.EventObject;
import java.util.EventListener;
import java.util.Hashtable;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.table.*;
import czt.animation.gui.util.*;

/**
 * The properties window displays the properties/events/methods/configuration of the currently
 * selected bean.
 */
public class PropertiesWindow extends JFrame implements PropertyChangeListener {
  /**
   * The bean that properties are being shown for.
   */
  protected Object bean=null;
  /**
   * The BeanInfo for bean's class.
   */
  protected BeanInfo beanInfo;
  /**
   * A label appearing at the top of the window identifying bean's type.
   * Plus an icon if that is provided by beanInfo.
   */
  protected JLabel headingTypeLabel;
  /**
   * A label appearing at the top of the window identifying bean's <code>name</code> property (if 
   * there is one).
   */
  protected JLabel headingNameLabel;

  /**
   * The tabbed pane that takes up most of this window.
   */
  protected JTabbedPane tabbedPane;
  /**
   * The PropertiesTable model that appears under the "Properties" tab.
   */
  protected PropertiesTable propertiesTable;
  /**
   * The EventsTable model that appears under the "Events" tab.
   */
  protected EventsTable eventsTable;
  /**
   * The MethodsTable model that appears under the "Methods" tab.
   */
  protected MethodsTable methodsTable;
  /**
   * The tables for properties events and methods.
   */
  protected JTable propertiesTableT, eventsTableT, methodsTableT;
  
  /**
   * Creates a properties window.
   */
  public PropertiesWindow() {
    getContentPane().setLayout(new BorderLayout());

    JPanel npanel=new JPanel(new GridLayout(1,2));
    
    npanel.add(headingTypeLabel=new JLabel());
    npanel.add(headingNameLabel=new JLabel());
    getContentPane().add(npanel,BorderLayout.NORTH);

    tabbedPane=new JTabbedPane();
    getContentPane().add(tabbedPane,BorderLayout.CENTER);
    propertiesTable=new PropertiesTable();
    tabbedPane.add("Properties",new JScrollPane(propertiesTableT=new JTable(propertiesTable) {
	protected void createDefaultEditors() {
	  defaultEditorsByColumnClass=new Hashtable();
	};
      }));

    propertiesTableT.setDefaultEditor(Object.class,new PropertyCellEditor());

//      Class[] editableClasses={Object.class,byte.class,double.class,float.class,int.class,long.class,short.class,boolean.class};
//      for(int i=0;i<editableClasses.length;i++)
//        propertiesTableT.setDefaultEditor(editableClasses[i],new PropertyCellEditor(propertiesTableT.getDefaultEditor(editableClasses[i])));
    
    //    TableColumn valuesColumn=propertiesTableT.getColumn("Value");
    //XXXvaluesColumn.setCellRenderer(new PropertyCellEditor());
    
    
    eventsTable=new EventsTable();
    tabbedPane.add("Events",new JScrollPane(eventsTableT=new JTable(eventsTable)));
    methodsTable=new MethodsTable();
    tabbedPane.add("Methods",new JScrollPane(methodsTableT=new JTable(methodsTable)));
    
    
    setBean(null);
    setSize(100,200);    
  };
  
  /**
   * Getter function for bean.
   */
  public Object getBean() {
    return bean;
  };
  /**
   * Setter function for bean.
   * Sets up the tables and labels, etc.
   */
  public void setBean(Object bean) {
    this.bean=bean;
    if(bean!=null)
      try {
	beanInfo=Introspector.getBeanInfo(bean.getClass());
	Image icon=beanInfo.getIcon(BeanInfo.ICON_COLOR_32x32);
	if(icon==null) icon=beanInfo.getIcon(BeanInfo.ICON_MONO_32x32);
	if(icon==null) icon=beanInfo.getIcon(BeanInfo.ICON_COLOR_16x16);
	if(icon==null) icon=beanInfo.getIcon(BeanInfo.ICON_MONO_16x16);
	if(icon==null)
	  headingTypeLabel.setIcon(null);
	else
	  headingTypeLabel.setIcon(new ImageIcon(icon));
	headingTypeLabel.setText(beanInfo.getBeanDescriptor().getName());
	String name=null;
	if(IntrospectionHelper.beanHasReadableProperty(bean,"name"))
	  name=(String)IntrospectionHelper.getBeanProperty(bean,"name");
	headingNameLabel.setText(name==null?"(unnamed)":name);
      } catch (IntrospectionException e) {
	System.err.println("COULDN'T GET BeanInfo");
	System.err.println(e);
      }
    else {
      beanInfo=null;
      headingTypeLabel.setText("(None)");
    }

    propertiesTable.setBean(bean);
    eventsTable.setBean(bean);
    methodsTable.setBean(bean);
    
    if(beanInfo==null)
      setTitle("Property Editor: (none)");
    else
      setTitle("Property Editor: "+beanInfo.getBeanDescriptor().getDisplayName());
    propertiesTableT.clearSelection();
    eventsTableT.clearSelection();
    if(beanInfo!=null) {
      if(beanInfo.getDefaultPropertyIndex()>=0)
	propertiesTableT.addRowSelectionInterval(beanInfo.getDefaultPropertyIndex(),
						 beanInfo.getDefaultPropertyIndex());
      if(beanInfo.getDefaultEventIndex()>=0)
	eventsTableT.addRowSelectionInterval(beanInfo.getDefaultEventIndex(),
					     beanInfo.getDefaultEventIndex());
    }
    methodsTableT.clearSelection();
    
  };


  /**
   * XXX Editor/Renderer class for properties.
   */
  static protected class PropertyCellEditor implements TableCellEditor {
    protected EventListenerList cellEditorListeners;
    public PropertyCellEditor() {
      cellEditorListeners=new EventListenerList();
      System.err.println("$$$$ In constructor");
      Thread.dumpStack();
    };
    protected Object clone() throws CloneNotSupportedException {
      System.err.println("$$$$ In clone");
      return super.clone();
    };


//      public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected,
//  						 int row, int column) {
//        //XXX...
//        //1. look up row to see if already got component for this row/column.
//        //2. if not
//        //2.1. create and register the component.
//        //2.2. register as FocusListener with component.
//        //3. If component isSelected mark it as current component.
//        //4. return the component.
//      };


    
    public Object getCellEditorValue(){
      //XXX...
      //Return the obj
      System.err.println("&&& in getCellEditorValue");
      return null;
    };
    public boolean isCellEditable(EventObject anEvent){
      System.err.println("&&& in isCellEditable");
      return true;//XXX PropertiesTable is responsible for saying what is editable
    };
    public boolean shouldSelectCell(EventObject anEvent){
      System.err.println("&&& in shouldSelectCell");
      return true;
    };
    public boolean stopCellEditing(){
      //XXX...
      System.err.println("&&& stopping cell editing");
      EventListener[] listeners=getListeners(CellEditorListener.class);
      for(int i=0;i<listeners.length;i++) 
	((CellEditorListener)listeners[i]).editingStopped(new ChangeEvent(this));
      return true;
    };
    public void cancelCellEditing(){
      //XXX...
      System.err.println("&&& canceling cell editing");
      EventListener[] listeners=getListeners(CellEditorListener.class);
      for(int i=0;i<listeners.length;i++) 
	((CellEditorListener)listeners[i]).editingCanceled(new ChangeEvent(this));
    };
    public void addCellEditorListener(CellEditorListener l){
      System.err.println("&&& in addCellEditorListener");
      cellEditorListeners.add(CellEditorListener.class, l);
    };
    public void removeCellEditorListener(CellEditorListener l){
      System.err.println("&&& in removeCellEditorListener");
      cellEditorListeners.remove(CellEditorListener.class, l);
    };
    

    public Object[] getListenerList(){
      System.err.println("&&& in getListenerList");
      return cellEditorListeners.getListenerList();
    };
    public EventListener[] getListeners(Class t) {
      System.err.println("&&& in getListeners");
      return cellEditorListeners.getListeners(t);
    };
    public int getListenerCount(){
      System.err.println("&&& in getListenerCount");
      return cellEditorListeners.getListenerCount();
    };
    public int getListenerCount(Class t){
      System.err.println("&&& in getListenerCount(Class)");
      return cellEditorListeners.getListenerCount(t);
    };
    
  

    //XXXX old \/    
    
    public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected,
						 int row, int column) {
      System.err.println("$$$$ in getTableCellEditorComponent");
      //XXX check its the right column?
      System.err.println("%%%%%%%%%%%%%%%%%%%%% Getting cell editor %%%%%%%%%%%%%%%%%%%%%%%%");
      
      Component c= ((PropertiesTable)table.getModel()).getEditor(row);
      System.err.println("%%% Editor is "+c);
      return c;      
    };
  };

  public void propertyChange(PropertyChangeEvent evt) {
    //XXX...
  };
};
