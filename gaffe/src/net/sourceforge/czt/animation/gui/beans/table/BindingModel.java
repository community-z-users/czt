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

public class BindingModel extends AbstractTableModel {
  private ZBinding binding=new ZBinding();
  private Vector keys=new Vector();
  
  public ZBinding getBinding() {return binding;};
  public void setBinding(ZBinding binding) {
    if(binding==null)binding=new ZBinding();
    this.binding=binding;
    keys=new Vector(binding.keySet());
  };
  
  public int getRowCount() {
    return keys.size();
  };
  public int getColumnCount() {
    return 2;
  };
  public String getColumnName(int column) {
    switch(column) {
     case 0:return "Name:";
     case 1:return "Value:";
     default:return "###ERROR###";
    }
  }
  public Object getValueAt(int row, int column) {
    return binding.get((String)keys.get(row));
  };
  public boolean isCellEditable(int rowIndex, int columnIndex) {
    return false;
  };
};
