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
import net.sourceforge.czt.animation.gui.temp.ZTuple;

public class TupleSetModel extends AbstractTableModel {
  private ZSet tupleSet=new ZSet();
  private int columnCount=0;
  
  public ZSet getTupleSet() {return tupleSet;};
  public void setTupleSet(ZSet tupleSet) {
    if(tupleSet==null) tupleSet=new ZSet();
    columnCount=0;
    try {
      if(tupleSet.size()>0)
	columnCount=((ZTuple)tupleSet.get(0)).size();
    } catch (ClassCastException ex) {
      throw new IllegalArgumentException("TupleSetModel must be given a ZSet of ZTuples.");
    }
    this.tupleSet=tupleSet;
    System.err.println("TupleSet = "+tupleSet);
    System.err.println("#TupleSet = "+tupleSet.size());
 
    fireTableDataChanged();
  };
  
  public int getRowCount() {
    return tupleSet.size();
  };
  public int getColumnCount() {
    return columnCount;
  };
  public String getColumnName(int column) {
    return ""+(column+1);
  }
  public Object getValueAt(int row, int column) {
    ZTuple t=(ZTuple)tupleSet.get(row);
    if(column<t.size()) return t.get(column);
    else return "";
  };
  public boolean isCellEditable(int rowIndex, int columnIndex) {
    return false;
  };
};
