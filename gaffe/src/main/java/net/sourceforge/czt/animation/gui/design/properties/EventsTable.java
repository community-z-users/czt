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
import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.util.Vector;

import javax.swing.event.TableModelEvent;
import javax.swing.table.AbstractTableModel;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * The table model of events that a bean provides that appears in the
 * properties window.
 * @see net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow
 */
final class EventsTable extends AbstractTableModel
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -5864396599010731482L;

private PropertiesWindow propertiesWindow;

  /**
   * The bean that this table is for.
   */
  private Object bean_;

  /**
   * The bean info for <code>bean_</code>'s class.
   */
  private BeanInfo beanInfo_;

  private final Vector<EventSetDescriptor> eventDescriptors = new Vector<EventSetDescriptor>();

  /**
   * Creates an events table without specifying a bean to look at.
   */
  public EventsTable(PropertiesWindow window)
  {
    this(null, window);
  };

  /**
   * Creates an events table looking at the events of <code>bean</code>.
   */
  public EventsTable(Object bean, PropertiesWindow window)
  {
    setBean(bean);
    propertiesWindow = window;
  };

  public void setEventDescriptors()
  {
    eventDescriptors.clear();
    if (beanInfo_ == null)
      return;
    EventSetDescriptor[] descriptors = beanInfo_.getEventSetDescriptors();
    for (int i = 0; i < descriptors.length; i++) {
      if ((propertiesWindow.getHiddenShown() || !descriptors[i].isHidden())
          && (propertiesWindow.getExpertShown() || !descriptors[i].isExpert())
          && (!propertiesWindow.getOnlyPreferredShown() || descriptors[i]
              .isPreferred())
          && (propertiesWindow.getTransientShown() || !Boolean.TRUE
              .equals(descriptors[i].getValue("transient"))))
        eventDescriptors.add(descriptors[i]);
    }
    fireTableChanged(new TableModelEvent(this));
    fireTableStructureChanged();
  };

  /**
   * Setter function for bean_.
   */
  public void setBean(Object bean)
  {
    bean_ = bean;
    beanInfo_ = null;
    if (bean_ != null)
      try {
        beanInfo_ = Introspector.getBeanInfo(bean_.getClass());
      } catch (IntrospectionException e) {
        System.err.println("COULDN'T GET BeanInfo");
        System.err.println(e);
      };
    setEventDescriptors();
  };

  /**
   * Returns the number of rows in this table.  Inherited from
   * <code>AbstractTableModel</code>.
   */
  public int getRowCount()
  {
    return eventDescriptors.size();
  };

  /**
   * Returns the number of columns in this table.  Inherited from
   * <code>AbstractTableModel</code>.
   */
  public int getColumnCount()
  {
    return 2;
  };

  /**
   * Returns the name of columns in this table.  Inherited from
   * <code>AbstractTableModel</code>.
   */
  public String getColumnName(int column)
  {
    switch (column) {
      case 0 :
        return "Event name";
      case 1 :
        return "Listener type";
      default :
        return "ERROR";
    }
  };

  /**
   * Returns the value stored in each cell of this table.
   * Inherited from <code>AbstractTableModel</code>.
   */
  public Object getValueAt(int row, int column)
  {
    EventSetDescriptor esd = (EventSetDescriptor) eventDescriptors.get(row);
    switch (column) {
      case 0 :
        return esd.getDisplayName();
      case 1 :
        return IntrospectionHelper.translateClassName(esd.getListenerType());
      default :
        return "ERROR";
    }
  };
};
