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
    System.err.println("!!!!!!!!Checking isCellEditable in PropertiesTable");
    boolean b= (column==2&&
		IntrospectionHelper.beanHasWritableProperty(bean,
							    beanInfo.getPropertyDescriptors()[row]
							    .getDisplayName())&&
		PropertyEditorManager.findEditor(beanInfo.getPropertyDescriptors()[row]
						 .getPropertyType())!=null);
    System.err.println(b?"yes":"no");
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
//      if(column==2)
//        IntrospectionHelper.setBeanProperty(bean,beanInfo.getPropertyDescriptors()[row]
//  					  .getName(),value);
//      else
//        super.setValueAt(value,row,column);
  };

  /**
   * The editors for the property in each row.
   */
  Vector editorComponents;//Vector<Component>
  Vector propertyEditors; //Vector<PropertyEditor>
  /**
   * Returns the editor for a particular row.
   */
  public Component getEditor(final int row) {
    Component component;
    PropertyEditor pe;
    System.err.println("@@@@ in getEditor("+row+")");
    try {
      component=(Component)editorComponents.get(row);

      if(component!=null) {
	System.err.println("@@@@ Did get component from editorComponents");
	return component;
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
      System.err.println("Shouldn't get ArrayIndexOutOfBoundsException from editorComponents");
      throw new Error(ex);
      //XXX this condition shouldn't happen error?
    };
    System.err.println("@@@@ Didn't get component from editorComponents");
    try {
      pe=(PropertyEditor)propertyEditors.get(row);
    } catch (ArrayIndexOutOfBoundsException ex) {
      System.err.println("Shouldn't get ArrayIndexOutOfBoundsException from propertyEditors");
      throw new Error(ex);
      //XXX this condition shouldn't happen error?
    };
    
    try {
      pe=PropertyEditorManager.findEditor(beanInfo.getPropertyDescriptors()[row].getPropertyType());
      System.err.println("@@@@ Did find editor from PropertyEditorManager");
      propertyEditors.set(row,pe);
    } catch (ArrayIndexOutOfBoundsException ex) {
      System.err.println("Shouldn't get ArrayIndexOutOfBoundsException from propertyEditors");
      throw new Error(ex);
      //XXX this condition shouldn't happen error?
    };
    if(pe==null) {
      System.err.println("Couldn't get PropertyEditorManager for class "+beanInfo.getPropertyDescriptors()[row].getPropertyType());
      return null;
    }
    
    pe.setValue(getObject(row));
    if(pe.supportsCustomEditor()) {
      System.err.println("@@@@ Did get custom editor component from PropertyEditor");
      Component editor=pe.getCustomEditor();
      editorComponents.set(row,editor);
      return editor;
    }
    System.err.println("@@@@ Didn't get custom editor component from PropertyEditor");
    final String[] tags=pe.getTags();
    final PropertyEditor pe2=pe;
    if(tags!=null) {
      System.err.println("@@@@ PropertyEditor did list tags");
      JComboBox editor=new JComboBox(tags);
      editor.setSelectedItem(pe.getAsText());
      editor.addItemListener(new ItemListener() {
	  public void itemStateChanged(ItemEvent e) {
	    pe2.setValue(getObject(row));
	    pe2.setAsText((String)e.getItem());
	  };
	});
      editorComponents.set(row,editor);
      return editor;
    }
    System.err.println("@@@@ PropertyEditor didn't list tags");
      
    JTextField editor=new JTextField(pe.getAsText());
    editor.addActionListener(new ActionListener() {
	public void actionPerformed(ActionEvent ev) {
	  pe2.setValue(getObject(row));
	  try {
	    pe2.setAsText(((JTextField)ev.getSource()).getText());
	  } catch (IllegalArgumentException ex) {
	    JOptionPane.showMessageDialog((JTextField)ev.getSource(),"Badly formatted property");
	  };
	};
      });
    
    return editor;
  };
};
