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

import net.sourceforge.czt.animation.gui.temp.ZTuple;

public class TupleModel extends AbstractTableModel {
  private ZTuple tuple=new ZTuple();
  private boolean vertical=true;

  public ZTuple getTuple() {return tuple;};
  public void setTuple(ZTuple tuple) {
    if(tuple==null)tuple=new ZTuple();
    this.tuple=tuple;
  };

  public boolean isVertical() {return vertical;};
  public void setVertical(boolean v) {vertical=v;};
  
  public int getRowCount() {return vertical?tuple.size():1;};
  public int getColumnCount() {return vertical?1:tuple.size();};
  public String getColumnName(int column) {
    if(vertical) return "Entries:";
    else return ""+(column+1);
  }
  public Object getValueAt(int row, int column) {
    if(vertical) return tuple.get(row);
    else return tuple.get(column);
  };
  public boolean isCellEditable(int rowIndex, int columnIndex) {
    return false;
  };
};
