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

/**
 * Table Model for displaying Z Relations (i.e. ZSets of ZTuples of size 2).
 */
public class RelationModel extends AbstractTableModel
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -7240742906611821569L;
private ZSet relation_ = new ZSet();

  public ZSet getRelation()
  {
    return relation_;
  };

  public void setRelation(ZSet relation)
  {
    if (relation == null)
      relation_ = new ZSet();
    else {
      try {
        if (relation.size() > 0 && ((ZTuple) relation.get(0)).size() != 2)
          throw new IllegalArgumentException("RelationModel must be given a "
              + "ZSet of ZTuples of size 2.");
      } catch (ClassCastException ex) {
        throw new IllegalArgumentException(
            "RelationModel must be given a ZSet " + "of ZTuples of size 2.");
      }
      relation_ = relation;
    }
    System.err.println("Relation = " + relation_);
    System.err.println("#Relation = " + relation_.size());

    fireTableDataChanged();
  };

  public int getRowCount()
  {
    return relation_.size();
  };

  public int getColumnCount()
  {
    return 2;
  };

  public String getColumnName(int column)
  {
    switch (column) {
      case 0 :
        return "Source:";
      case 1 :
        return "Target:";
      default :
        return "###ERROR###";
    }
  }

  public Object getValueAt(int row, int column)
  {
    System.err.println("(" + row + ")Tuple=" + relation_.get(row));
    System.err.println("(" + row + ")Value(" + column + ")="
        + ((ZTuple) relation_.get(row)).get(column));
    return ((ZTuple) relation_.get(row)).get(column);
  };

  public boolean isCellEditable(int rowIndex, int columnIndex)
  {
    return false;
  };
};
