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

package net.sourceforge.czt.animation.gui.beans.table;

import java.util.Vector;

import javax.swing.table.AbstractTableModel;

import net.sourceforge.czt.animation.gui.temp.ZBinding;

/**
 * Table Model for displaying
 * {@link net.sourceforge.czt.animation.gui.temp.ZBinding ZBinding}s.
 */
public class BindingModel extends AbstractTableModel
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 3806474933101234111L;

private ZBinding binding_ = new ZBinding();

  private Vector<String> keys_ = new Vector<String>();

  public ZBinding getBinding()
  {
    return binding_;
  };

  public void setBinding(ZBinding binding)
  {
    if (binding == null)
      binding_ = new ZBinding();
    else
      binding_ = binding;
    keys_ = new Vector<String>(binding_.keySet());
  };

  public int getRowCount()
  {
    return keys_.size();
  };

  public int getColumnCount()
  {
    return 2;
  };

  public String getColumnName(int column)
  {
    switch (column) {
      case 0 :
        return "Name:";
      case 1 :
        return "Value:";
      default :
        return "###ERROR###";
    }
  }

  public Object getValueAt(int row, int column)
  {
    return binding_.get((String) keys_.get(row));
  };

  public boolean isCellEditable(int rowIndex, int columnIndex)
  {
    return false;
  };
};
