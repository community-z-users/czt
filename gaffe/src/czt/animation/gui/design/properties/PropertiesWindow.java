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

import czt.animation.gui.design.BeanSelectedListener;
import czt.animation.gui.design.BeanSelectedEvent;
import czt.animation.gui.util.IntrospectionHelper;

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
    tabbedPane.add("Events",new JScrollPane(eventsTableT=new JTable(eventsTable