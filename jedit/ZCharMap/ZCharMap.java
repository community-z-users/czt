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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.*;

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

  private JComboBox markup;

  private RenderingHints renderingHints;

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

    org.gjt.sp.jedit.textarea.TextAreaPainter textAreaPainter =
      mView.getTextArea().getPainter();
    HashMap hints = new HashMap();
    if (textAreaPainter.isAntiAliasEnabled()) {
      hints.put(RenderingHints.KEY_ANTIALIASING,
		RenderingHints.VALUE_ANTIALIAS_ON);
      hints.put(RenderingHints.KEY_TEXT_ANTIALIASING,
		RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
    }
    else {
      hints.put(RenderingHints.KEY_ANTIALIASING,
		RenderingHints.VALUE_ANTIALIAS_OFF);
      hints.put(RenderingHints.KEY_TEXT_ANTIALIASING,
		RenderingHints.VALUE_TEXT_ANTIALIAS_OFF);
    }
    if (textAreaPainter.isFractionalFontMetricsEnabled()) {
      hints.put(RenderingHints.KEY_FRACTIONALMETRICS,
		RenderingHints.VALUE_FRACTIONALMETRICS_ON);
    }
    else {
      hints.put(RenderingHints.KEY_FRACTIONALMETRICS,
		RenderingHints.VALUE_FRACTIONALMETRICS_OFF);
    }
    renderingHints = new RenderingHints(hints);

    JPanel buttonRow = new JPanel();
    markup = new JComboBox(new String[] { "LaTeX Markup", "Unicode Markup" });
    buttonRow.add(markup);
    JButton typecheckButton = new JButton("Typecheck");
    typecheckButton.addActionListener(new TypecheckHandler());
    buttonRow.add(typecheckButton);
    JButton unicodeButton = new JButton("toUnicode");
    unicodeButton.addActionListener(new UnicodeHandler());
    buttonRow.add(unicodeButton);
    JButton latexButton = new JButton("toLatex");
    latexButton.addActionListener(new LatexHandler());
    buttonRow.add(latexButton);
    JButton xmlButton = new JButton("toXML");
    xmlButton.addActionListener(new XmlHandler());
    buttonRow.add(xmlButton);
    add(BorderLayout.NORTH, buttonRow);

    mTable = new JTable(new ZCharTable());
    mTable.setFont(view.getTextArea().getPainter().getFont());
    mTable.getColumnModel().getColumn(0).setMinWidth(90);
    mTable.setRowHeight(view.getTextArea().getPainter().getFont().getSize()+4);
    mTable.setFocusable(false);
    mTable.setDefaultRenderer(ZChar.class, new StringRenderer(true));
    mTable.setDefaultRenderer(String.class, new StringRenderer(false));
    mTable.setRowSelectionAllowed(false);
    mTable.setColumnSelectionAllowed(false);
    mTable.setAutoResizeMode(JTable.AUTO_RESIZE_NEXT_COLUMN);
    mTable.addMouseListener(new MouseHandler());
    mTable.addMouseMotionListener(new MouseHandler());
    
    add(BorderLayout.CENTER,new JScrollPane(mTable));
    
    status = new StatusRenderer(" ");
    status.setFont(view.getTextArea().getPainter().getFont());
    add(BorderLayout.SOUTH,status);
    setFocusable(false);
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
      { "Paragraphs",
	new ZChar("Sect",
		  "\u2500 section NAME parents standard_toolkit \u2029\n",
		  "\\begin{zsection}\n  \\SECTION NAME \\parents standard\\_toolkit\n\\end{zsection}\n",
		  "Section Header"),
	new ZChar("Op",
		  "\u2500\n  function 42 leftassoc ( _ op _ )\n\u2029\n",
		  "\\begin{zed}\n  \\function 42 \\leftassoc ( \\varg op \\varg )\n\\end{zed}\n",
		  "Operator Template"),
	new ZChar("[G]",
		  "\u2500 [  ] \u2029\n",
		  "\\begin{zed}\n  [  ]\n\\end{zed}\n",
		  "Given Sets"),
	new ZChar("Ax",
		  "\u2577\n  \n|\n  \n\u2029\n",
		  "\\begin{axdef}\n  \n\\where\n  \n\\end{axdef}\n",
		  "Axiomatic Definition"),
	new ZChar("::=",
		  "\u2500\n  TYPE ::= FOO | BAR\u300ATYPE\u300B\n\u2029\n",
		  "\\begin{zed}\n  TYPE ::= FOO | BAR \\ldata TYPE \\rdata\n\\end{zed}\n",
		  "Freetype Definition"),
	new ZChar("==",
		  "\u2500\n  NAME == \n\u2029\n",
		  "\\begin{zed}\n  NAME == \n\\end{zed}\n",
		  "Horizontal Definition"),
	new ZChar("SCH",
		  "\u250C NAME\n  \n|\n  \n\u2029\n",
		  "\\begin{schema}{NAME}\n  \n\\where\n  \n\\end{schema}\n",
		  "Schema Definition"),
	new ZChar("\u22A2?",
		  "\u2500\n  \u22A2? \n\u2029\n",
		  "\\begin{zed}\n  \\vdash? \n\\end{zed}\n",
		  "Conjecture")
      },
      { "Predicates",
	new ZChar("\u2200", "\\forall", "Universal Quantification"),
	new ZChar("\u2203", "\\exists", "Existential Quantification"),
	new ZChar("\u2227", "\\land", "Conjunction"),
	new ZChar("\u2228", "\\lor", "Disjunction"),
	new ZChar("\u00AC", "\\lnot", "Negation"),
	new ZChar("\u21D2", "\\implies", "Implication"),
	new ZChar("\u21D4", "\\iff", "Equivalence"),
	new ZChar("\u2260", "\\neq", "Not Equal"),
	new ZChar("\u2208", "\\in", "Membership"),
	new ZChar("\u2209", "\\notin", "Not Member"),
    	new ZChar("\u2286", "\\subseteq", "Subset Of Or Equal To"),    
	new ZChar("\u2282", "\\subset", "Subset Of")
      },
      { "Sets",
	new ZChar("\u2119", "\\power", "Power Set"),
	new ZChar("{", "\\{", "Begin Set"),
	new ZChar("|", "|", "Such That"),
	new ZChar("\u2981", "@", "Returning"),
	new ZChar("}", "\\}", "End Set"),
	new ZChar("\u2205", "\\emptyset", "Empty Set"),
	new ZChar("\u222A", "\\cup", "Union"),
	new ZChar("\u22C3", "\\bigcup", "n-ary Union"),
	new ZChar("\u2229", "\\cap", "Intersection"),
	new ZChar("\u22C2", "\\bigcap", "n-ary Intersection"),
	new ZChar("\\", "\\setminus", "Set Subtraction"),
	new ZChar("\u2296", "\\symdiff", "Symmetric Difference")
      },
      { "Relations",
	new ZChar("\u2194", "\\rel", "Relation"),
	new ZChar("\u21A6", "\\mapsto", "Mapsto"),
	new ZChar("\u00D7", "\\cross", "Cartesian Product"),
	new ZChar("\u25C1", "\\dres", "Domain Restriction"),
	new ZChar("\u2A64", "\\ndres", "Domain Subtraction"),
	new ZChar("\u25B7", "\\rres", "Range Restriction"),
	new ZChar("\u2A65", "\\nrres", "Range Substraction"),
	new ZChar("\u2295", "\\oplus", "Relational Overriding"),
	new ZChar("\u2A3E", "\\comp", "Relational Composition"),
	new ZChar("\u223C", "\\inv", "Relational Inverse"),
	new ZChar("\u2987", "\\limg", "Left Image"),
	new ZChar("\u2988", "\\rimg", "Right Image")
      },
      { "Functions",
	new ZChar("\u2192", "\\fun", "Total Function"),
	new ZChar("\u21F8", "\\pfun", "Partial Function"),
	new ZChar("\u2914", "\\pinj", "Partial Injection"),
	new ZChar("\u21A3", "\\inj", "Total Injection"),
	new ZChar("\u2900", "\\psurj", "Partial Surjection"),
	new ZChar("\u2916", "\\bij", "Total Bijection"),
	new ZChar("\u21FB", "\\ffun", "Finite Function"),
	new ZChar("\u2915", "\\finj", "Finite Injection"),
	new ZChar("\u03BB", "\\lambda", "Lambda"),
	new ZChar("\u03BC", "\\mu", "Mu (Choice)")
      },
      { "Sequences",
	new ZChar("\u27E8", "\\langle", "Begin Sequence"),
	new ZChar("\u27E9", "\\rangle", "End Sequence"),
	new ZChar("\u2040", "\\cat", "Concatenation"),
	new ZChar("\u2040/", "\\dcat", "Distributed Concatenation"),
	new ZChar("\u21BF", "\\extract", "Extract"),
	new ZChar("\u21BE", "\\filter", "Filter"),
	new ZChar("#", "\\#", "Size")
      },
      { "Arithmetic",
	new ZChar("\u2124", "\\num", "Integers"),
	new ZChar("\u2115", "\\nat", "Natural Numbers"),
	new ZChar("+", "+", "Binary Plus"),
	new ZChar("\u2212", "-", "Binary Minus"),
	new ZChar("-", "\\negate", "Unary Negation"),
	new ZChar("*", "*", "Multiplication"),
	new ZChar("div", "\\div", "Integer Division"),
	new ZChar("mod", "\\mod", "Integer Modulo"),
	new ZChar("\u2264", "\\leq", "Less Than"),
	new ZChar("\u2265", "\\geq", "Greater Than")
      },
      { "Schemas",
	new ZChar("\u0394", "\\Delta", "Delta"),
	new ZChar("\u039E", "\\Xi", "Xi"),
	new ZChar("\u03B8", "\\theta", "Theta"),
	new ZChar("\u2989", "\\lblot", "Left Binding"),
	new ZChar("\u298A", "\\rblot", "Right Binding"),
	new ZChar("\u29F9", "\\hide", "Schema Hiding"),
	new ZChar("\u2A21", "\\project", "Schema Projection"),
	new ZChar("\u2A1F", "\\semi", "Sequential Composition"),
	new ZChar("\u2A20", "\\pipe", "Schema Piping")
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
	ZChar zchar = (ZChar) mTable.getModel().getValueAt(row,col);
	if (markup.getSelectedIndex() == 0) {
	  mView.getTextArea().setSelectedText(zchar.getLatex());
	}
	else {
	  mView.getTextArea().setSelectedText(zchar.getUnicode());
	}
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
	status.setText("Char: " + zchar.getUnicode()
		       + " Hex: " + zchar.getHexString()
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

  class TypecheckHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      try {
	SectionManager manager = new SectionManager();
	String filename = mView.getBuffer().getPath();
	Term term = ParseUtils.parse(filename, manager);
	net.sourceforge.czt.typecheck.util.impl.Factory factory =
	  new net.sourceforge.czt.typecheck.util.impl.Factory(
	    new net.sourceforge.czt.z.impl.ZFactoryImpl());
	SectTypeEnv sectTypeEnv = new SectTypeEnv(factory);
	TypeAnnotatingVisitor typeVisitor =
	  new TypeAnnotatingVisitor(sectTypeEnv, manager);
	TypeChecker typechecker = new TypeChecker(manager);
	term.accept(typeVisitor);
	term.accept(typechecker);
      }
      catch (Exception exception) {
	System.err.println(exception.getMessage());
      }
    }
  }

  class UnicodeHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      System.err.println(mView.getBuffer().getPath());
    }
  }

  class LatexHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      System.err.println(mView.getBuffer().getPath());
    }
  }

  class XmlHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      try {
	SectionManager manager = new SectionManager();
	String filename = mView.getBuffer().getPath();
	Term term = ParseUtils.parse(filename, manager);
	net.sourceforge.czt.z.jaxb.JaxbXmlWriter writer =
	  new net.sourceforge.czt.z.jaxb.JaxbXmlWriter();
	Buffer buffer = jEdit.newFile(mView);
	java.io.StringWriter out = new java.io.StringWriter();
	writer.write(term, out);
	out.close();
	buffer.insert(0, out.toString());
      }
      catch (Exception exception) {
	System.err.println(exception.getMessage());
      }
    }
  }

  /**
   * A string renderer which centers the given string onto a JLabel.
   */
  class StringRenderer extends DefaultTableCellRenderer {
    public StringRenderer(boolean centered)
    {
      super();
      setFont(mView.getTextArea().getPainter().getFont());
      if (centered) {
	setHorizontalAlignment(CENTER);
	setVerticalAlignment(CENTER);
      }
    }

    public Component getTableCellRendererComponent(JTable table,
						   Object zchar, 
						   boolean isSelected,
						   boolean hasFocus,
						   int row,
						   int column) {
      setText(zchar.toString());
      return this;
    }

    protected void paintComponent(Graphics graphics)
    {
      if (graphics instanceof Graphics2D) {
	Graphics2D g2D = (Graphics2D) graphics;
	g2D.setRenderingHints(renderingHints);
      }
      super.paintComponent(graphics);
    }
  }

  /**
   * A string renderer which centers the given string onto a JLabel.
   */
  class StatusRenderer extends JLabel {
    public StatusRenderer(String string)
    {
      super(string);
      setFont(mView.getTextArea().getPainter().getFont());
    }

    protected void paintComponent(Graphics graphics)
    {
      if (graphics instanceof Graphics2D) {
	Graphics2D g2D = (Graphics2D) graphics;
	g2D.setRenderingHints(renderingHints);
      }
      super.paintComponent(graphics);
    }
  }
}

