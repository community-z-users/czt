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

package net.sourceforge.czt.animation.gui.design.properties.renderers;

import java.awt.Component;

import javax.swing.JLabel;
import javax.swing.JTable;
import javax.swing.border.Border;
import javax.swing.table.TableCellRenderer;

/**
 * <code>TableCellRenderer</code> for displaying <code>Border</code>s.
 */
public class BorderRenderer extends JLabel implements TableCellRenderer
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -5132997362448118459L;

public BorderRenderer()
  {
    setOpaque(true);
  };

  public Component getTableCellRendererComponent(JTable table, Object value,
      boolean isSelected, boolean hasFocus, int row, int column)
  {
    System.err.println(value);
    Class<?>[] classes = value.getClass().getInterfaces();
    for (int i = 0; i < classes.length; i++)
      System.err.println(classes[i]);
    System.err.println(value.getClass().getSuperclass());

    setBorder((Border) value);
    System.err.println("###");
    return this;
  };
};
