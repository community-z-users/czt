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

import javax.swing.table.AbstractTableModel;

import net.sourceforge.czt.animation.gui.temp.ZSet;

public class SetModel extends AbstractTableModel {
  private ZSet set=new ZSet();
  public ZSet getSet() {return set;};
  public void setSet(ZSet set) {
    if(set==null) set=new ZSet();
    this.set=set;
    System.err.println("Set = "+set);
    System.err.println("#Set = "+set.size());
 
    fireTableDataChanged();
  };
  
  public int getRowCount() {
    return set.size();
  };
  public int getColumnCount() {
    return 1;
  };
  public String getColumnName(int column) {
    switch(column) {
     case 0:return "Members:";
     default:return "###ERROR###";
    }
  }
  public Object getValueAt(int row, int column) {
    return set.get(row);
  };
  public boolean isCellEditable(int rowIndex, int columnIndex) {
    return false;
  };
};
