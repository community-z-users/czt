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

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.GridLayout;
import java.awt.Image;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.KeyEvent;
import java.beans.BeanInfo;
import java.beans.Customizer;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyDescriptor;
import java.beans.PropertyEditor;
import java.util.EventListener;
import java.util.EventObject;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map;

import javax.swing.AbstractAction;
import javax.swing.AbstractButton;
import javax.swing.Action;
import javax.swing.ActionMap;
import javax.swing.Box;
import javax.swing.ImageIcon;
import javax.swing.InputMap;
import javax.swing.JButton;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.event.CellEditorListener;
import javax.swing.event.ChangeEvent;
import javax.swing.event.EventListenerList;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;

import net.sourceforge.czt.animation.gui.design.BeanSelectedEvent;
import net.sourceforge.czt.animation.gui.design.BeanSelectedListener;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The properties window displays the properties/events/methods/configuration of
 * the currently selected bean.
 */
public final class PropertiesWindow extends JFrame
    implements
      BeanSelectedListener
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -4532211069430536158L;

/**
   * The bean that properties are being shown for.
   */
  private Object bean_ = null;

  /**
   * The <code>BeanInfo</code> for <code>bean_</code>'s class.
   */
  private BeanInfo beanInfo_;

  /**
   * A label appearing at the top of the window identifying bean_'s type.
   * Plus an icon if that is provided by beanInfo_.
   */
  private JLabel headingTypeLabel_;

  /**
   * A label appearing at the top of the window identifying bean_'s
   * <code>name</code> property (if there is one).
   */
  private JLabel headingNameLabel_;

  private JButton customiserButton_;

  /**
   * The tabbed pane that takes up most of this window.
   */
  private JTabbedPane tabbedPane_;

  /**
   * The PropertiesTable model that appears under the "Properties" tab.
   */
  private final PropertiesTable propertiesTable_;

  /**
   * The EventsTable model that appears under the "Events" tab.
   */
  private final EventsTable eventsTable_;

  /**
   * The MethodsTable model that appears under the "Methods" tab.
   */
  private final MethodsTable methodsTable_;

  /**
   * The tables for properties events and methods.
   */
  private JTable propertiesTableT_, eventsTableT_, methodsTableT_;

  private boolean hiddenShown_ = false, expertShown_ = false;

  private boolean onlyPreferredShown_ = false, transientShown_ = false;

  private boolean onlyEditableShown_ = false;

  private JCheckBoxMenuItem hiddenShownCB_, expertShownCB_;

  private JCheckBoxMenuItem onlyPreferredShownCB_, transientShownCB_;

  private JCheckBoxMenuItem onlyEditableShownCB_;

  private ActionMap actionMap = new ActionMap();

  private InputMap inputMap = new InputMap();

  private void setDescriptors()
  {
    propertiesTable_.setPropertyDescriptors();
    eventsTable_.setEventDescriptors();
    methodsTable_.setMethodDescriptors();
  };

  private void setHiddenShown(boolean b)
  {
    hiddenShown_ = b;
    if (hiddenShownCB_.isSelected() != b)
      hiddenShownCB_.setSelected(b);
    setDescriptors();
  };

  private void setExpertShown(boolean b)
  {
    expertShown_ = b;
    if (expertShownCB_.isSelected() != b)
      expertShownCB_.setSelected(b);
    setDescriptors();
  };

  private void setOnlyPreferredShown(boolean b)
  {
    onlyPreferredShown_ = b;
    if (onlyPreferredShownCB_.isSelected() != b)
      onlyPreferredShownCB_.setSelected(b);
    setDescriptors();
  };

  private void setTransientShown(boolean b)
  {
    transientShown_ = b;
    if (transientShownCB_.isSelected() != b)
      transientShownCB_.setSelected(b);
    setDescriptors();
  };

  private void setOnlyEditableShown(boolean b)
  {
    onlyEditableShown_ = b;
    if (onlyEditableShownCB_.isSelected() != b)
      onlyEditableShownCB_.setSelected(b);
    propertiesTable_.setPropertyDescriptors();
  };

  boolean getHiddenShown()
  {
    return hiddenShown_;
  };

  boolean getExpertShown()
  {
    return expertShown_;
  };

  boolean getOnlyPreferredShown()
  {
    return onlyPreferredShown_;
  };

  boolean getTransientShown()
  {
    return transientShown_;
  };

  boolean getOnlyEditableShown()
  {
    return onlyEditableShown_;
  };

  private void registerAction(Action action, String name, KeyStroke key)
  {
    action.putValue(Action.NAME, name);
    action.putValue(Action.SHORT_DESCRIPTION, name);
    action.putValue(Action.LONG_DESCRIPTION, name);
    //XXX action.putValue(Action.SMALL_ICON,...);
    //XXX action.putValue(Action.ACTION_COMMAND_KEY,...);
    action.putValue(Action.ACCELERATOR_KEY, key);
    //XXX action.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put(name, action);
    inputMap.put(key, name);
  };

  private void setupActions(ActionMap am, InputMap im)
  {
    actionMap.setParent(am);
    inputMap.setParent(im);

    getLayeredPane().setActionMap(actionMap);
    getLayeredPane().setInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,
        inputMap);

    Action action_show_hidden_descriptors = new AbstractAction(
        "Show hidden descriptors")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -8445096317956137024L;

	public void actionPerformed(ActionEvent e)
      {
        if (e.getSource() instanceof AbstractButton)
          setHiddenShown(((AbstractButton) e.getSource()).isSelected());
        else
          setHiddenShown(!getHiddenShown());
      };
    };
    registerAction(action_show_hidden_descriptors, "Show hidden descriptors",
        KeyStroke.getKeyStroke("control H"));

    Action action_show_expert_descriptors = new AbstractAction(
        "Show expert descriptors")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 1761858462024879226L;

	public void actionPerformed(ActionEvent e)
      {
        if (e.getSource() instanceof AbstractButton)
          setExpertShown(((AbstractButton) e.getSource()).isSelected());
        else
          setExpertShown(!getExpertShown());
      };
    };
    registerAction(action_show_expert_descriptors, "Show expert descriptors",
        KeyStroke.getKeyStroke("control E"));

    Action action_show_onlyPreferred_descriptors = new AbstractAction(
        "Only show preferred descriptors")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -1905918719614412375L;

	public void actionPerformed(ActionEvent e)
      {
        if (e.getSource() instanceof AbstractButton) {
          AbstractButton ab = (AbstractButton) e.getSource();
          setOnlyPreferredShown(ab.isSelected());
        }
        else {
          setOnlyPreferredShown(!getOnlyPreferredShown());
        }
      };
    };
    registerAction(action_show_onlyPreferred_descriptors,
        "Only show preferred descriptors", KeyStroke.getKeyStroke("control P"));

    Action action_show_transient_descriptors = new AbstractAction(
        "Show transient descriptors")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 3123607846797724566L;

	public void actionPerformed(ActionEvent e)
      {
        if (e.getSource() instanceof AbstractButton)
          setTransientShown(((AbstractButton) e.getSource()).isSelected());
        else
          setTransientShown(!getTransientShown());
      };
    };
    registerAction(action_show_transient_descriptors,
        "Show transient descriptors", KeyStroke.getKeyStroke("control T"));

    Action action_show_onlyEditable_descriptors = new AbstractAction(
        "Only show editable properties")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 639388793374507061L;

	public void actionPerformed(ActionEvent e)
      {
        if (e.getSource() instanceof AbstractButton) {
          AbstractButton ab = (AbstractButton) e.getSource();
          setOnlyEditableShown(ab.isSelected());
        }
        else {
          setOnlyEditableShown(!getOnlyEditableShown());
        }
      };
    };
    registerAction(action_show_onlyEditable_descriptors,
        "Only show editable properties", KeyStroke.getKeyStroke("control D"));
  };

  private void setupMenus()
  {
    JMenuBar mb = new JMenuBar();
    JMenu file = new JMenu("File");
    file.add(new JMenuItem(actionMap.get("Quit")));

    JMenu filter = new JMenu("Filter");
    filter.setMnemonic(KeyEvent.VK_V);
    hiddenShownCB_ = new JCheckBoxMenuItem(actionMap
        .get("Show hidden descriptors"));
    filter.add(hiddenShownCB_);
    expertShownCB_ = new JCheckBoxMenuItem(actionMap
        .get("Show expert descriptors"));
    filter.add(expertShownCB_);
    onlyPreferredShownCB_ = new JCheckBoxMenuItem(actionMap
        .get("Only show preferred descriptors"));
    filter.add(onlyPreferredShownCB_);
    transientShownCB_ = new JCheckBoxMenuItem(actionMap
        .get("Show transient descriptors"));
    filter.add(transientShownCB_);
    onlyEditableShownCB_ = new JCheckBoxMenuItem(actionMap
        .get("Only show editable properties"));
    filter.add(onlyEditableShownCB_);

    JMenu help = new JMenu("Help");
    help.setMnemonic(KeyEvent.VK_H);
    help.add(new JMenuItem(actionMap.get("About...")));
    help.add(new JMenuItem(actionMap.get("License...")));

    mb.add(file);
    mb.add(filter);
    mb.add(Box.createHorizontalGlue());
    mb.add(help);
    setJMenuBar(mb);
  };

  /**
   * Creates a properties window.
   */
  public PropertiesWindow(ActionMap am, InputMap im)
  {
    getContentPane().setLayout(new BorderLayout());

    setupActions(am, im);
    setupMenus();

    JPanel npanel = new JPanel(new GridLayout(1, 2));

    npanel.add(headingTypeLabel_ = new JLabel());
    npanel.add(headingNameLabel_ = new JLabel());
    npanel.add(customiserButton_ = new JButton("Customiser"));
    customiserButton_.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ev)
      {
        //XXX Creation of the customiser, etc. should probably be done in
        //    setBean instead.
        Customizer customiser;
        try {
          Class<?> customiserClass = beanInfo_.getBeanDescriptor()
              .getCustomizerClass();
          customiser = (Customizer) customiserClass.newInstance();
        } catch (Exception ex) {
          System.err.println("Exception while creating customiser (ignoring):"
              + ex);
          customiserButton_.setEnabled(false);
          return;
        };
        JDialog cDialog = new JDialog(PropertiesWindow.this, beanInfo_
            .getBeanDescriptor().getName()
            + " Customiser", true);
        customiser.setObject(bean_);
        customiser.addPropertyChangeListener(new PropertyChangeListener()
        {
          public void propertyChange(PropertyChangeEvent ev)
          {
            propertiesTable_.fireTableDataChanged();
          };
        });

        cDialog.getContentPane().add((Component) customiser);
        cDialog.pack();
        cDialog.setVisible(true);
      };
    });
    getContentPane().add(npanel, BorderLayout.NORTH);

    tabbedPane_ = new JTabbedPane();
    getContentPane().add(tabbedPane_, BorderLayout.CENTER);
    propertiesTable_ = new PropertiesTable(this);
    propertiesTableT_ = new JTable(propertiesTable_)
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 3624800651478485823L;

	@SuppressWarnings("rawtypes")
	protected void createDefaultEditors()
      {
        defaultEditorsByColumnClass = new Hashtable();
      };
    };
    tabbedPane_.add("Properties", new JScrollPane(propertiesTableT_));
    propertiesTableT_.setDefaultEditor(Object.class, new PropertyCellEditor());
    propertiesTableT_.setDefaultRenderer(Object.class,
        new PropertyCellRenderer());
    propertiesTableT_.setDefaultRenderer(String.class, new OtherRenderer());

    eventsTable_ = new EventsTable(this);
    eventsTableT_ = new JTable(eventsTable_);
    tabbedPane_.add("Events", new JScrollPane(eventsTableT_));

    methodsTable_ = new MethodsTable(this);
    methodsTableT_ = new JTable(methodsTable_);
    tabbedPane_.add("Methods", new JScrollPane(methodsTableT_));

    setBean(null);
    setSize(500, 500);
  };

  /**
   * Setter function for bean_.
   * Sets up the tables and labels, etc.
   */
  private void setBean(Object bean)
  {
    PropertyChangeListener beanNameChangeListener = new PropertyChangeListener()
    {
      public void propertyChange(PropertyChangeEvent evt)
      {
        if (evt.getPropertyName().equals("name")) {
          String name = (String) evt.getNewValue();
          if (name == null)
            headingNameLabel_.setText("(unnamed)");
          else
            headingNameLabel_.setText(name);
        }
      };
    };

    if (this.bean_ != null)
      IntrospectionHelper.removeBeanListener(this.bean_,
          PropertyChangeListener.class, beanNameChangeListener);
    this.bean_ = bean;
    customiserButton_.setEnabled(false);
    if (bean_ != null)
      try {
        beanInfo_ = Introspector.getBeanInfo(bean_.getClass());
        Image icon = beanInfo_.getIcon(BeanInfo.ICON_COLOR_32x32);
        if (icon == null)
          icon = beanInfo_.getIcon(BeanInfo.ICON_MONO_32x32);
        if (icon == null)
          icon = beanInfo_.getIcon(BeanInfo.ICON_COLOR_16x16);
        if (icon == null)
          icon = beanInfo_.getIcon(BeanInfo.ICON_MONO_16x16);
        if (icon == null)
          headingTypeLabel_.setIcon(null);
        else
          headingTypeLabel_.setIcon(new ImageIcon(icon));
        headingTypeLabel_.setText(beanInfo_.getBeanDescriptor().getName());
        String name = null;
        if (IntrospectionHelper.beanHasReadableProperty(bean_, "name"))
          name = (String) IntrospectionHelper.getBeanProperty(bean_, "name");
        headingNameLabel_.setText(name == null ? "(unnamed)" : name);
      } catch (IntrospectionException e) {
        System.err.println("COULDN'T GET BeanInfo");
        System.err.println(e);
      }
    else {
      beanInfo_ = null;
      headingTypeLabel_.setText("(None)");
    }

    propertiesTable_.setBean(bean_);
    eventsTable_.setBean(bean_);
    methodsTable_.setBean(bean_);

    if (beanInfo_ == null)
      setTitle("Property Editor: (none)");
    else
      setTitle("Property Editor: "
          + beanInfo_.getBeanDescriptor().getDisplayName());
    propertiesTableT_.clearSelection();
    eventsTableT_.clearSelection();
    if (beanInfo_ != null) {
      if (beanInfo_.getDefaultPropertyIndex() >= 0) {
        int dpidx = beanInfo_.getDefaultPropertyIndex();
        propertiesTableT_.addRowSelectionInterval(dpidx, dpidx);
      }
      if (beanInfo_.getDefaultEventIndex() >= 0) {
        int deidx = beanInfo_.getDefaultEventIndex();
        eventsTableT_.addRowSelectionInterval(deidx, deidx);
      }
      if (beanInfo_.getBeanDescriptor().getCustomizerClass() != null)
        customiserButton_.setEnabled(true);
    }
    methodsTableT_.clearSelection();
    if (this.bean_ != null)
      IntrospectionHelper.addBeanListener(this.bean_,
          PropertyChangeListener.class, beanNameChangeListener);
  };

  public void beanSelected(BeanSelectedEvent ev)
  {
    setBean(ev.getSelectedBean());
  };

  /**
   * <code>TableCellEditor</code> for editing the property fields.
   * Gives different editor component's for each property type.
   */
  private final class PropertyCellEditor implements TableCellEditor
  {
    private static final int CS_NONE = 0;

    private static final int CS_CUSTOM_EDITOR = 1;

    private static final int CS_TAGS = 2;

    private static final int CS_STRING = 3;

    private int componentSource;

    private EventListenerList cellEditorListeners;

    private Component currentComponent;

    private PropertyEditor propertyEditor;

    private PropertyDescriptor propertyDescriptor;

    public PropertyCellEditor()
    {
      cellEditorListeners = new EventListenerList();
      currentComponent = null;
      componentSource = CS_NONE;
      propertyDescriptor = null;
      propertyEditor = null;
    };

    public Component getTableCellEditorComponent(JTable table, Object value,
        boolean isSelected, int row, int column)
    {
      //XXX will cancel or stop have been called first to tidy away the old
      //    editor?

      propertyDescriptor = propertiesTable_.getPropertyDescriptor(row);
      propertyEditor = IntrospectionHelper.getEditor(propertyDescriptor
          .getPropertyType());
      Object propertyValue = IntrospectionHelper.getBeanProperty(bean_,
          propertyDescriptor);
      propertyEditor.setValue(propertyValue);
      propertyEditor.addPropertyChangeListener(new PropertyChangeListener()
      {
        public void propertyChange(PropertyChangeEvent evt)
        {
          IntrospectionHelper.setBeanProperty(bean_, propertyDescriptor,
              propertyEditor.getValue());
          //XXX Nasty nasty hack, because Component objects don't send a
          //    PropertyChange event when their 'name' property changes.
          if (bean_ instanceof Component
              && propertyDescriptor.getName().equals("name")) {
            System.err.println("SENDING PropertyChangeEvents for name");
            PropertyChangeEvent event = new PropertyChangeEvent(bean_, "name",
                null, propertyEditor.getValue());
            PropertyChangeListener[] listeners = ((Component) bean_)
                .getPropertyChangeListeners();
            for (int i = 0; i < listeners.length; i++) {
              listeners[i].propertyChange(event);
              System.err.println(i + 1);
            }
            listeners = ((Component) bean_).getPropertyChangeListeners("name");
            for (int i = 0; i < listeners.length; i++) {
              listeners[i].propertyChange(event);
              System.err.println("" + (i + 1) + "b");
            }
          }
        };
      });
      //XXX I probably need to add a PropertyChangeListener to actually write
      //    the edited values into the bean.
      String[] tags;
      if (propertyEditor.supportsCustomEditor()) {
        final Window window;
        final Component component = propertyEditor.getCustomEditor();
        if (component instanceof Window) {
          window = (Window) component;
        }
        else {
          final JDialog dialog = new JDialog((JFrame) null, "Edit property: "
              + beanInfo_.getBeanDescriptor().getName() + "."
              + propertyDescriptor.getName(), true);
          dialog.getContentPane().setLayout(new BorderLayout());
          dialog.getContentPane().add(component, BorderLayout.CENTER);
          dialog.pack();
          window = dialog;
        }
        final JButton button = new JButton("Edit");
        button.addActionListener(new ActionListener()
        {
          public void actionPerformed(ActionEvent ev)
          {
            window.setVisible(true);
          };
        });

        currentComponent = button;
        componentSource = CS_CUSTOM_EDITOR;
      }
      else if ((tags = propertyEditor.getTags()) != null) {
        currentComponent = new JComboBox<>(tags);
        componentSource = CS_TAGS;
        JComboBox<?> cb = (JComboBox<?>) currentComponent;
        cb.setSelectedItem(propertyEditor.getAsText());
        cb.addItemListener(new ItemListener()
        {
          public void itemStateChanged(ItemEvent e)
          {
            //XXX ? Should I be changing the property here, or wait until
            //    editing is stopped?
          }
        });
      }
      else {
        currentComponent = new JTextField(propertyEditor.getAsText());
        componentSource = CS_STRING;
        ((JTextField) currentComponent).addActionListener(new ActionListener()
        {
          public void actionPerformed(ActionEvent ev)
          {
            //XXX is this necessary?
            stopCellEditing();
          };
        });
      }
      System.err.println("*** currentComponent=" + currentComponent);
      System.err.println("*** componentSource=" + componentSource);
      return currentComponent;

      //XXX...
      //1. look up row to see if already got component for this row/column.
      //2. if not
      //2.1. create and register the component.
      //2.2. register as FocusListener with component.
      //3. If component isSelected mark it as current component.
      //4. return the component.
    };

    public Object getCellEditorValue()
    {
      if (componentSource == CS_CUSTOM_EDITOR) {
        return propertyEditor.getValue();
      }
      else if (componentSource == CS_TAGS) {
        return (String) ((JComboBox<?>) currentComponent).getSelectedItem();
      }
      else if (componentSource == CS_STRING) {
        return (String) ((JTextField) currentComponent).getText();
      }
      else {
        throw new Error("PropertyCellEditor.getCellEditorValue() shouldn't be "
            + "getting called when it doesn't have a component");
      }
      //xxx...
    };

    public boolean isCellEditable(EventObject anEvent)
    {
      //XXX we're relying on the table model to say yeah or nay on this.
      return true;
    };

    public boolean shouldSelectCell(EventObject anEvent)
    {
      return true;
    };

    public boolean stopCellEditing()
    {
      System.err.println("*** currentComponent=" + currentComponent);
      System.err.println("*** componentSource=" + componentSource);
      //XXX Don't need to save values here.
      //    JTable is listening for editingStopped events, calls setValueAt in
      //XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
      if (componentSource == CS_CUSTOM_EDITOR) {
        //XXX can I assume that the custom editor will handle changing the bean?
      }
      else if (componentSource == CS_TAGS) {
        //XXX should I combine CS_TAGS and CS_STRING getting the value from
        //    getCellEditorValue()
        JComboBox<?> cb = (JComboBox<?>) currentComponent;
        propertyEditor.setAsText((String) cb.getSelectedItem());
      }
      else if (componentSource == CS_STRING) {
        try {
          JTextField tf = (JTextField) currentComponent;
          propertyEditor.setAsText((String) tf.getText());
        } catch (IllegalArgumentException ex) {
          JOptionPane.showMessageDialog(PropertiesWindow.this,
              "Badly formatted property");
          return false;
        };
      }
      else {
        throw new Error("PropertyCellEditor.stopCellEditing() shouldn't be "
            + "getting called when it doesn't have a component");
      }

      //Let all the listeners know editing has stopped.
      EventListener[] listeners = cellEditorListeners
          .getListeners(CellEditorListener.class);
      for (int i = 0; i < listeners.length; i++) {
        CellEditorListener listener = (CellEditorListener) listeners[i];
        listener.editingStopped(new ChangeEvent(this));
      }

      componentSource = CS_NONE; //Cut off the now unused component.
      currentComponent = null; //XXX maybe I should reuse it if possible?
      propertyEditor = null;
      propertyDescriptor = null;
      //xxx...
      return true;
    };

    public void cancelCellEditing()
    {
      //Let all the listeners know editing has stopped.
      EventListener[] listeners = cellEditorListeners
          .getListeners(CellEditorListener.class);
      for (int i = 0; i < listeners.length; i++) {
        CellEditorListener listener = (CellEditorListener) listeners[i];
        listener.editingCanceled(new ChangeEvent(this));
      }
      componentSource = CS_NONE; //Cut off the now unused component.
      currentComponent = null; //XXX maybe I should reuse it if possible?
      propertyEditor = null;
      propertyDescriptor = null;
      //xxx...
    };

    //Functions delegating to cellEditorListeners
    public void addCellEditorListener(CellEditorListener l)
    {
      cellEditorListeners.add(CellEditorListener.class, l);
    };

    public void removeCellEditorListener(CellEditorListener l)
    {
      cellEditorListeners.remove(CellEditorListener.class, l);
    };

    @SuppressWarnings("unused")
	public Object[] getListenerList()
    {
      return cellEditorListeners.getListenerList();
    };

    @SuppressWarnings("unused")
    public EventListener[] getListeners(Class<EventListener> t)
    {
      return cellEditorListeners.getListeners(t);
    };

    @SuppressWarnings("unused")
    public int getListenerCount()
    {
      return cellEditorListeners.getListenerCount();
    };

    @SuppressWarnings("unused")
    public int getListenerCount(Class<?> t)
    {
      return cellEditorListeners.getListenerCount(t);
    };
  };

  /**
   * Default renderer for properties.
   * Disables the component displaying non-editable properties, so that they
   * appear greyed out.
   */
  private class OtherRenderer extends DefaultTableCellRenderer
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 7919753638859608807L;

	public Component getTableCellRendererComponent(JTable table, Object value,
        boolean isSelected, boolean hasFocus, int row, int column)
    {
      int valueColumn = table.getColumn("Value").getModelIndex();
      boolean isEditable = propertiesTable_.isCellEditable(row, valueColumn);
      Component component = super.getTableCellRendererComponent(table, value,
          isSelected, hasFocus, row, column);
      component.setEnabled(isEditable);
      return component;
    }
  };

  /**
   * <code>TableCellRenderer</code> for displaying the property fields.
   * Gives different renderer component's for each property type.
   */
  private class PropertyCellRenderer implements TableCellRenderer
  {
    private DefaultTableCellRenderer defaultRenderer = new DefaultTableCellRenderer();

    public Component getTableCellRendererComponent(JTable table, Object value,
        boolean isSelected, boolean hasFocus, int row, int column)
    {
      boolean isEditable = propertiesTable_.isCellEditable(row, column);
      Component component;
      if (value != null)
        for (Map.Entry<Class<?>,TableCellRenderer> entry : defaultRenderers.entrySet()) {
          Class<?> clazz = entry.getKey();
          TableCellRenderer renderer = entry.getValue();
          if (clazz.isAssignableFrom(value.getClass())) {
            component = renderer.getTableCellRendererComponent(table, value,
                isSelected, hasFocus, row, column);
            component.setEnabled(isEditable);
            return component;
          }
        };
      component = defaultRenderer.getTableCellRendererComponent(table, value,
          isSelected, hasFocus, row, column);
      component.setEnabled(isEditable);
      return component;
    };
  };

  private static final Map<Class<?>, TableCellRenderer> defaultRenderers = new HashMap<Class<?>, TableCellRenderer>();

  public static void addDefaultRenderer(Class<?> c, TableCellRenderer r)
  {
    defaultRenderers.put(c, r);
  };
};
