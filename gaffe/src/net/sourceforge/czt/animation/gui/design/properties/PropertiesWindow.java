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

import net.sourceforge.czt.animation.gui.design.BeanSelectedListener;
import net.sourceforge.czt.animation.gui.design.BeanSelectedEvent;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

import java.awt.BorderLayout;             import java.awt.Component;
import java.awt.GridLayout;               import java.awt.Image;

import java.awt.event.ActionEvent;        import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;          import java.awt.event.ItemListener;

import java.beans.BeanInfo;               import java.beans.IntrospectionException;
import java.beans.Introspector;           import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener; import java.beans.PropertyEditor;
import java.beans.PropertyEditorManager;

import java.lang.reflect.Method;

import java.util.EventObject;             import java.util.EventListener;
import java.util.Hashtable;

import javax.swing.ImageIcon;             import javax.swing.JComboBox;
import javax.swing.JFrame;                import javax.swing.JLabel;
import javax.swing.JOptionPane;           import javax.swing.JPanel;
import javax.swing.JScrollPane;           import javax.swing.JTabbedPane;
import javax.swing.JTable;                import javax.swing.JTextField;

import javax.swing.event.CellEditorListener;
import javax.swing.event.ChangeEvent;     import javax.swing.event.EventListenerList;

import javax.swing.table.TableCellEditor;


/**
 * The properties window displays the properties/events/methods/configuration of the currently
 * selected bean.
 */
public class PropertiesWindow extends JFrame implements BeanSelectedListener {
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

  PropertyChangeListener beanNameChangeListener=new PropertyChangeListener() {
      public void propertyChange(PropertyChangeEvent evt) {
	if(evt.getPropertyName().equals("name")) {
	  String name=(String)evt.getNewValue();
	  headingNameLabel.setText(name==null?"(unnamed)":name);
	}
      };
    };
  
  /**
   * Setter function for bean.
   * Sets up the tables and labels, etc.
   */
  public void setBean(Object bean) {
    if(this.bean!=null)
      IntrospectionHelper.removeBeanListener(this.bean,PropertyChangeListener.class, 
					     beanNameChangeListener);
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
    if(this.bean!=null)
      IntrospectionHelper.addBeanListener(this.bean,PropertyChangeListener.class,
					  beanNameChangeListener);
  };


  /**
   * XXX Editor/Renderer class for properties.
   */
  protected class PropertyCellEditor implements TableCellEditor {
    protected EventListenerList cellEditorListeners;
    protected Component currentComponent;
    protected PropertyEditor propertyEditor;
    protected String propertyName;
    
    protected int componentSource;
    protected static final int CS_NONE=0;
    protected static final int CS_CUSTOM_EDITOR=1;
    protected static final int CS_TAGS=2;
    protected static final int CS_STRING=3;

    public PropertyCellEditor() {
      cellEditorListeners=new EventListenerList();
      currentComponent=null;
      componentSource=CS_NONE;
      propertyName=null;
      propertyEditor=null;
    };

    public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected,
  						 int row, int column) {
      System.err.println("*** In getTableCellEditorComponent");
      //XXX will cancel or stop have been called first to tidy away the old editor?
      propertyEditor=PropertyEditorManager.findEditor(beanInfo.getPropertyDescriptors()[row]
						      .getPropertyType());
      System.err.println("!!! bean type="+beanInfo.getBeanDescriptor().getName());
      System.err.println("!!! property name="+beanInfo.getPropertyDescriptors()[row].getName());
      System.err.println("!!! property type="+beanInfo.getPropertyDescriptors()[row].getPropertyType());
      if(propertyEditor==null) System.err.println("propertyEditor=( null )");
      
      propertyName=beanInfo.getPropertyDescriptors()[row].getName();
      propertyEditor.setValue(propertiesTable.getObject(row));
      propertyEditor.addPropertyChangeListener(new PropertyChangeListener() {
	  public void propertyChange(PropertyChangeEvent evt) {
	    System.err.println("### "
			       +"In PropertyChangeListener.propertyChange attached to propertyEditor");
	    System.err.println("### "
			       +"source = "+evt.getSource());
	    System.err.println("### "
			       +"newValue = "+propertyEditor.getValue());
	    System.err.println("### "
			       +"propagationId = "+evt.getPropagationId());
	    System.err.println("### "
			       +"propertyName = "+propertyName);
	    System.err.println("### "
			       +"bean = "+bean);
	    IntrospectionHelper.setBeanProperty(bean,propertyName,propertyEditor.getValue());
	    //XXX Nasty nasty hack, because Component objects don't send a PropertyChange event when 
	    //their 'name' property changes.
	    if(bean instanceof Component && propertyName.equals("name")) {
	      System.err.println("SENDING PropertyChangeEvents for name");
	      PropertyChangeEvent event=new PropertyChangeEvent(bean,"name",null,
								propertyEditor.getValue());
	      PropertyChangeListener[] listeners=((Component)bean).getPropertyChangeListeners();
	      for(int i=0;i<listeners.length;i++) {
		listeners[i].propertyChange(event);
		System.err.println(i+1);
	      }
	      listeners=((Component)bean).getPropertyChangeListeners("name");
	      for(int i=0;i<listeners.length;i++) {
		listeners[i].propertyChange(event);
		System.err.println(""+(i+1)+"b");
	      }
	    }
	  };
	});
      //XXX I probably need to add a PropertyChangeListener to actually write the edited values into 
      //    the bean.
      String[] tags;
      if(propertyEditor.supportsCustomEditor()) {
	currentComponent=propertyEditor.getCustomEditor();
	componentSource=CS_CUSTOM_EDITOR;
      } else if((tags=propertyEditor.getTags())!=null) {
	currentComponent=new JComboBox(tags);
	componentSource=CS_TAGS;
	((JComboBox)currentComponent).setSelectedItem(propertyEditor.getAsText());
	((JComboBox)currentComponent).addItemListener(new ItemListener() {
	    public void itemStateChanged(ItemEvent e) {
	      //XXX ? Should I be changing the property here, or wait until editing is stopped?
	    }
	  });
      } else {      
	currentComponent=new JTextField(propertyEditor.getAsText());
	componentSource=CS_STRING;
	((JTextField)currentComponent).addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent ev) {
	      //XXX is this necessary?
	      stopCellEditing();
	    };
	  });
      }
      System.err.println("*** currentComponent="+currentComponent);
      System.err.println("*** componentSource="+componentSource);
      return currentComponent;
      
      //XXX...
      //1. look up row to see if already got component for this row/column.
      //2. if not
      //2.1. create and register the component.
      //2.2. register as FocusListener with component.
      //3. If component isSelected mark it as current component.
      //4. return the component.
    };

    
    
    public Object getCellEditorValue(){
      if(componentSource==CS_CUSTOM_EDITOR) {
	return propertyEditor.getValue();
      } else if(componentSource==CS_TAGS) {
	return (String)((JComboBox)currentComponent).getSelectedItem();
      } else if(componentSource==CS_STRING) {
	return (String)((JTextField)currentComponent).getText();
      } else {
	throw new Error("PropertyCellEditor.getCellEditorValue() shouldn't be getting called when it "
			+"doesn't have a component");
      }
      //xxx...      
    };
    public boolean isCellEditable(EventObject anEvent){
      return true;//XXX we're relying on the table model to say yeah or nay on this.
    };
    public boolean shouldSelectCell(EventObject anEvent){
      return true;
    };
    public boolean stopCellEditing(){
      System.err.println("*** currentComponent="+currentComponent);
      System.err.println("*** componentSource="+componentSource);
      //XXX Don't need to save values here.
      //    JTable is listening for editingStopped events, calls setValueAt in 
      //XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
      if(componentSource==CS_CUSTOM_EDITOR) {
	//XXX can I assume that the custom editor will handle changing the bean?
      } else if(componentSource==CS_TAGS) {
	//XXX should I combine CS_TAGS and CS_STRING getting the value from getCellEditorValue()
	propertyEditor.setAsText((String)((JComboBox)currentComponent).getSelectedItem());
      } else if(componentSource==CS_STRING) {
	try {
	  propertyEditor.setAsText((String)((JTextField)currentComponent).getText());
	} catch(IllegalArgumentException ex) {
	  JOptionPane.showMessageDialog(PropertiesWindow.this,"Badly formatted property");
	  return false;
	};
      } else {
	throw new Error("PropertyCellEditor.stopCellEditing() shouldn't be getting called when it "
			+"doesn't have a component");
      }

      //Let all the listeners know editing has stopped.
      EventListener[] listeners=cellEditorListeners.getListeners(CellEditorListener.class);
      for(int i=0;i<listeners.length;i++)
	((CellEditorListener)listeners[i]).editingStopped(new ChangeEvent(this));
      
      
      componentSource=CS_NONE;//Cut off the now unused component.
      currentComponent=null;  //XXX maybe I should reuse it if possible?
      propertyEditor=null;
      propertyName=null;
      //xxx...
      return true;
    };
    public void cancelCellEditing(){
      System.err.println("*** currentComponent="+currentComponent);
      System.err.println("*** componentSource="+componentSource);
      //Let all the listeners know editing has stopped.
      EventListener[] listeners=cellEditorListeners.getListeners(CellEditorListener.class);
      for(int i=0;i<listeners.length;i++)
	((CellEditorListener)listeners[i]).editingCanceled(new ChangeEvent(this));

      componentSource=CS_NONE;//Cut off the now unused component.
      currentComponent=null;  //XXX maybe I should reuse it if possible?
      propertyEditor=null;
      propertyName=null;
      //xxx...
    };


    //Functions delegating to cellEditorListeners
    public void addCellEditorListener(CellEditorListener l){
      cellEditorListeners.add(CellEditorListener.class, l);
    };
    public void removeCellEditorListener(CellEditorListener l){
      cellEditorListeners.remove(CellEditorListener.class, l);
    };

    public Object[] getListenerList(){
      return cellEditorListeners.getListenerList();
    };
    public EventListener[] getListeners(Class t) {
      return cellEditorListeners.getListeners(t);
    };
    public int getListenerCount(){
      return cellEditorListeners.getListenerCount();
    };
    public int getListenerCount(Class t){
      return cellEditorListeners.getListenerCount(t);
    };
  };
  
  public void beanSelected(BeanSelectedEvent ev) {
    setBean(ev.getSelectedBean());
  };
};
