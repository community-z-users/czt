/*
 * ZCharMap.java
 * Copyright 2003 Mark Utting
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
 
import java.awt.event.*;
import java.awt.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.table.*;
import javax.swing.*;

import org.gjt.sp.jedit.*;

/**
 * <p>A window containing a Z character map.</p>
 *
 * <p>This character map can be used to insert Z unicode characters
 * into a jedit editor window.</p>
 *
 * @author Petra Malik
 * @czt.todo Think about the font to use and the size of the table
 *           (especially how to handle resizing and the first column).
 */
public class ZCharMap extends JPanel
{
  //############################################################
  //##################### MEMBER VARIABLES #####################
  //############################################################

  /**
   * The jedit view.
   */
  private View mView;

  /**
   * The table.
   */
  private JTable mTable;

  /**
   * The status bar label.
   */
  private JLabel status;
  
  //############################################################
  //####################### CONSTRUCTOR ########################
  //############################################################

  /**
   * Constructs a Z character map.
   *
   * @param view the jedit view where the characters are inserted.
   */
  public ZCharMap(View view)
  {
    super(new BorderLayout());

    mView = view;
    mTable = new JTable(new ZCharTable());
    mTable.setFont(view.getTextArea().getPainter().getFont());
    mTable.getColumnModel().getColumn(0).setMinWidth(90);
    mTable.setRowHeight(30);
    mTable.setDefaultRenderer(ZChar.class, new StringRenderer());
    mTable.setRowSelectionAllowed(false);
    mTable.setColumnSelectionAllowed(false);
    mTable.setAutoResizeMode(JTable.AUTO_RESIZE_NEXT_COLUMN);
    mTable.addMouseListener(new MouseHandler());
    mTable.addMouseMotionListener(new MouseHandler());
    
    add(BorderLayout.CENTER,new JScrollPane(mTable));
    
    status = new JLabel(" ");
    status.setFont(view.getTextArea().getPainter().getFont());
    add(BorderLayout.SOUTH,status);
  }

  //############################################################
  //###################### INNER CLASSES #######################
  //############################################################

  /**
   * A table model for the Z character table.
   */
  class ZCharTable extends AbstractTableModel
  {
    /**
     * An array of objects where the first column contains strings
     * (the heading for the corresponding row) and all other columns
     * contain ZChar objects.
     */
    private final Object[][] mTableArray = {
      { "Sets",
	new ZChar('\u2115', "Natural Numbers"),
	new ZChar('\u2119', "Power Set"),
	new ZChar('\u2205', "Empty Set"),
	new ZChar('\u222A', "Union"),
	new ZChar('\u22C3', "n-ary Union"),
	new ZChar('\u2229', "Intersection"),
	new ZChar('\u22C2', "n-ary Intersection"),   
    	new ZChar('\u2286', "Subset Of Or Equal To"),    
	new ZChar('\u2282', "Subset Of")
      },
      { "Relations",
	new ZChar('\u2194', "Relation"),
	new ZChar('\u00D7', "Cartesian Product"),
	new ZChar('\u25B7', "Domain Restriction"),
	new ZChar('\u2A64', "Domain Subtraction"),
	new ZChar('\u2A3E', "Relational Composition"),
	new ZChar('\u2295', "Relational Overriding")
      },
      { "Functions",
	new ZChar('\u2192', "Function"),
	new ZChar('\u21F8', "Partial Function"),
	new ZChar('\u2914', "Partial Injection"),
	new ZChar('\u21A3', "Total Injection"),
	new ZChar('\u2900', "Partial Surjection"),
	new ZChar('\u2916', "Total Bijection"),
	new ZChar('\u21FB', "Finite Function"),
	new ZChar('\u2915', "Finite Injection")
      },
      { "Predicates",
	new ZChar('\u2200', "Universal Quantification"),
	new ZChar('\u2203', "Existential Quantification"),
	new ZChar('\u2227', "Conjunction"),
	new ZChar('\u2228', "Disjunction"),
	new ZChar('\u00AC', "Negation"),
	new ZChar('\u21D2', "Implication"),
	new ZChar('\u21D4', "Equivalence")
      },
      { "Sequences",
	new ZChar('\u2329', "Begin Sequence"),
	new ZChar('\u232A', "End Sequence"),
	new ZChar('\u2040', "Concatenation")
      },
      { "Misc",
	new ZChar('\u2A21', "Schema Projection"),
	new ZChar('\u2A1F', "Schema Composition"),
	new ZChar('\u2A20', "Schema Piping")
      }
    };

    /**
     * Returns the maximum length of all the rows.
     *
     * @return the number of columns in this table.
     */
    public int getColumnCount()
    {
      int erg = 0;
      for(int i=0; i<mTableArray.length; i++) {
	if (mTableArray[i].length > erg) erg = mTableArray[i].length;
      }
      return erg;
    }

    /**
     * Returns the number of rows.
     *
     * @return the number of rows in this table.
     */
    public int getRowCount()
    {
      return mTableArray.length;
    }
    
    /**
     * Gets the object at the specified position.
     * If no object can be found the empty string
     * is returned.
     *
     * @return the object at the specified position
     *         or the empty string (should never be
     *         <code>null</code>). 
     */
    public Object getValueAt(int row, int col)
    {
      try {
	return mTableArray[row][col];
      } catch(IndexOutOfBoundsException e) {
	return "";
      }
    }

    /**
     * Returns <code>String.class</code> if <code>col</code>
     * is zero, <code>ZChar.class</code> otherwise.
     * Note that this method does not take the actual classes
     * contained in table into account.
     *
     * @return <code>String.class</code> if <code>col</code>
     *         is zero, <code>ZChar.class</code> otherwise.
     */
    public Class getColumnClass(int col)
    {
      if (col==0) return String.class;
      return ZChar.class;
    }

    /**
     * Returns <code>null</code> regardless of the column number.
     *
     * @return <code>null</code>
     */
    public String getColumnName(int col)
    {
      return null;
    }
  }
  

  /**
   * The action handler.
   */  
  class ActionHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent event)
    {
      mTable.repaint();
    }
  }
  
  /**
   * The mouse handler.
   */
  class MouseHandler extends MouseInputAdapter
  {
    /**
     * Inserts the clicked character into the jedit editor window.
     */
    public void mouseClicked(MouseEvent event)
    {
      Point p = event.getPoint();
      int row = mTable.rowAtPoint(p);
      int col = mTable.columnAtPoint(p);
      if(row == -1 || col == -1 || col == 0) {
	status.setText(" ");
      } else {
	String ch = mTable.getModel().getValueAt(row,col).toString();
	mView.getTextArea().setSelectedText(ch);
      }
    }

    /**
     * Updates the status bar depending on the mouse position.
     */
    public void mouseMoved(MouseEvent event)
    {
      Point p = event.getPoint();
      int row = mTable.rowAtPoint(p);
      int col = mTable.columnAtPoint(p);
      Object o = mTable.getModel().getValueAt(row, col);
      if (o instanceof ZChar) {
	ZChar zchar = (ZChar) mTable.getModel().getValueAt(row, col);
	char c = zchar.getChar();
	status.setText("Char: " + c
		       + " Hex: " + Integer.toHexString(c)
		       + " Description: " + zchar.getDescription());
      } else {
	status.setText(" ");
      }
    }

    /**
     * Updates the status bar.
     */
    public void mouseExited(MouseEvent event)
    {
      status.setText(" ");
    }
  }

  /**
   * A string renderer which centers the given string onto a JLabel.
   */
  class StringRenderer extends JLabel implements TableCellRenderer {

    public StringRenderer()
    {
      super();
      setFont(mView.getTextArea().getPainter().getFont());
      setHorizontalAlignment(CENTER);
      setVerticalAlignment(CENTER);
    }

    public Component getTableCellRendererComponent(JTable table,
						   Object string, 
						   boolean isSelected,
						   boolean hasFocus,
						   int row,
						   int column) {
      setText(string.toString());
      return this;
    }
  }
}

