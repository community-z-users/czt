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

import java.awt.BorderLayout;             import java.awt.Component;
import java.awt.Window;

import java.awt.event.ActionEvent;        import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;          import java.awt.event.ItemListener;

import java.beans.BeanInfo;               import java.beans.IntrospectionException;
import java.beans.Introspector;           import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener; import java.beans.PropertyDescriptor;
import java.beans.PropertyEditor;         import java.beans.PropertyEditorManager;

import java.util.Enumeration;             import java.util.EventListener;
import java.util.EventObject;             import java.util.Vector;

import javax.swing.JButton;               import javax.swing.JComboBox;             
import javax.swing.JDialog;               import javax.swing.JFrame;
import javax.swing.JOptionPane;           import javax.swing.JPanel;                
import javax.swing.JTable;                import javax.swing.JTextField;

import javax.swing.event.CellEditorListener;
import javax.swing.event.ChangeEvent;
import javax.swing.event.EventListenerList;
import javax.swing.event.TableModelEvent;

import javax.swing.table.AbstractTableModel; import javax.swing.table.TableCellEditor;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The table model of properties that a bean provides that appears in the properties window.
 * @see net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow
 */
class PropertiesTable extends AbstractTableModel {

  public PropertiesTable(PropertiesWindow window) {
    setBean(null);
    propertiesWindow=window;
  };
  
  protected PropertiesWindow propertiesWindow;
  
  /**
   * The bean that this table is for.
   */
  protected Object bean;
  /**
   * The bean info for <code>bean</code>'s class.
   */
  protected BeanInfo beanInfo;
  
  protected final Vector/*<PropertyDescriptor>*/ propertyDescriptors=new Vector();  
  protected final Vector/*<Boolean>*/            propertyDescriptorsEditable=new Vector();  
  
  public final void setPropertyDescriptors() {
    propertyDescriptors.clear();
    propertyDescriptorsEditable.clear();
    if(beanInfo==null) return;
    PropertyDescriptor[] descriptors=beanInfo.getPropertyDescriptors();
    for(int i=0;i<descriptors.length;i++) {
      boolean isEditable=isCellEditable(descriptors[i]);
      if((    propertiesWindow.getHiddenShown()        ||!descriptors[i].isHidden())
	 && ( propertiesWindow.getExpertShown()        ||!descriptors[i].isExpert())
	 && (!propertiesWindow.getOnlyPreferredShown() || descriptors[i].isPreferred())
	 && ( propertiesWindow.getTransientShown()     ||!Boolean.TRUE.equals(descriptors[i]
									      .getValue("transient")))
	 && (!propertiesWindow.getOnlyEditableShown()  || isEditable)) {
	propertyDescriptors.add(descriptors[i]);
	propertyDescriptorsEditable.add(new Boolean(isEditable));
      }
    }      
    fireTableChanged(new TableModelEvent(this));
    fireTableStructureChanged();  
  };
  
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
  public Class getTypeAt(int row) {
    return ((PropertyDescriptor)propertyDescriptors.get(row)).getPropertyType();
  };

  protected Object getObject(int row) {
    return IntrospectionHelper.getBeanProperty(bean,((PropertyDescriptor)propertyDescriptors
						     .get(row)).getName());
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
  protected boolean isCellEditable(PropertyDescriptor pd) {
    return (IntrospectionHelper.beanHasWritableProperty(bean,pd.getDisplayName())
	    && PropertyEditorManager.findEditor(pd.getPropertyType())!=null);
  };
  
  /**
   * Returns true if a particular cell is editable.  Inherited from <code>AbstractTableModel</code>.
   */
  public boolean isCellEditable(int row, int column) {
    boolean b= (column==2&& ((Boolean)propertyDescriptorsEditable.get(row)).booleanValue());
    
//  		IntrospectionHelper.beanHasWritableProperty(bean,
//  							    ((PropertyDescriptor)propertyDescriptors
//  							     .get(row)).getDisplayName())
//  		&& PropertyEditorManager.findEditor(((PropertyDescriptor)propertyDescriptors.get(row))
//  						    .getPropertyType())!=null);
    return b;
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


  public TableCellEditor createTableCellEditor() {
    return new PropertyCellEditor();
  };
  
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
      propertyEditor=PropertyEditorManager.findEditor(getTypeAt(row));
      System.err.println("!!! bean type="+beanInfo.getBeanDescriptor().getName());
      System.err.println("!!! property name="
			 +((PropertyDescriptor)propertyDescriptors.get(row)).getName());
      System.err.println("!!! property type="+getTypeAt(row));
      if(propertyEditor==null) System.err.println("propertyEditor=( null )");
      
      propertyName=((PropertyDescriptor)propertyDescriptors.get(row)).getName();
      propertyEditor.setValue(getObject(row));
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
	final Window window;
	final Component component=propertyEditor.getCustomEditor();
	if(component instanceof Window) {
	  window=(Window)component;
	} else {
	  final JDialog dialog=new JDialog((JFrame)null,"Edit property: "+beanInfo.getBeanDescriptor().getName()+"."+propertyName,true);
	  dialog.getContentPane().setLayout(new BorderLayout());
	  dialog.getContentPane().add(component,BorderLayout.CENTER);
	  dialog.pack();
	  window=dialog;
	}
	final JButton button=new JButton("Edit");
	button.addActionListener(new ActionListener() {	    
	    public void actionPerformed(ActionEvent ev) {
	      window.setVisible(true);
	    };
	  });
	
	currentComponent=button;
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
	  JOptionPane.showMessageDialog(propertiesWindow,"Badly formatted property");
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

};
