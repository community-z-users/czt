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

import java.awt.Component;

import java.awt.event.ActionEvent;        import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;          import java.awt.event.ItemListener;

import java.beans.BeanInfo;               import java.beans.IntrospectionException;
import java.beans.Introspector;           import java.beans.PropertyDescriptor;
import java.beans.PropertyEditor;         import java.beans.PropertyEditorManager;

import java.util.Enumeration;

import java.util.Vector;

import javax.swing.JComboBox;             import javax.swing.JOptionPane;
import javax.swing.JTextField;

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
  
  public final void setPropertyDescriptors() {
    propertyDescriptors.clear();
    if(beanInfo==null) return;
    PropertyDescriptor[] descriptors=beanInfo.getPropertyDescriptors();
    for(int i=0;i<descriptors.length;i++) {
      if((    propertiesWindow.getHiddenShown()        ||!descriptors[i].isHidden())
	 && ( propertiesWindow.getExpertShown()        ||!descriptors[i].isExpert())
	 && (!propertiesWindow.getOnlyPreferredShown() || descriptors[i].isPreferred())
	 && ( propertiesWindow.getTransientShown()     ||!Boolean.TRUE.equals(descriptors[i]
									      .getValue("transient"))))
	propertyDescriptors.add(descriptors[i]);
    }      
    editorComponents.clear(); editorComponents.setSize(getRowCount()+1);
    propertyEditors.clear();  propertyEditors.setSize(getRowCount()+1);
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
  /**
   * Returns true if a particular cell is editable.  Inherited from <code>AbstractTableModel</code>.
   */
  public boolean isCellEditable(int row, int column) {
    System.err.println("!!!!!!!!Checking isCellEditable in PropertiesTable");
    boolean b= (column==2&&
		IntrospectionHelper.beanHasWritableProperty(bean,
							    ((PropertyDescriptor)propertyDescriptors
							     .get(row)).getDisplayName())
		&& PropertyEditorManager.findEditor(((PropertyDescriptor)propertyDescriptors.get(row))
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
  };

  /**
   * The editors for the property in each row.
   */
  protected final Vector editorComponents=new Vector/*<Component>*/();
  protected final Vector propertyEditors=new Vector/*<PropertyEditor>*/();

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
      pe=PropertyEditorManager.findEditor(((PropertyDescriptor)propertyDescriptors.get(row))
					  .getPropertyType());
      System.err.println("@@@@ Did find editor from PropertyEditorManager");
      propertyEditors.set(row,pe);
    } catch (ArrayIndexOutOfBoundsException ex) {
      System.err.println("Shouldn't get ArrayIndexOutOfBoundsException from propertyEditors");
      throw new Error(ex);
      //XXX this condition shouldn't happen error?
    };
    if(pe==null) {
      System.err.println("Couldn't get PropertyEditorManager for class "
			 +((PropertyDescriptor)propertyDescriptors.get(row)).getPropertyType());
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
