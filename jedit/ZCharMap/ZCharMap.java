/*
 * ZCharMap.java
 * Copyright (C) 2003, 2004, 2005 Mark Utting
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
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;
import javax.swing.event.*;
import javax.swing.table.*;
import javax.swing.*;

import org.gjt.sp.jedit.*;
import errorlist.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

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
  implements ParsePropertiesKeys
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

  private JButton convert_;

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
    markup.addActionListener(new MarkupHandler());
    buttonRow.add(markup);
    JButton typecheckButton = new JButton("Typecheck");
    typecheckButton.addActionListener(new TypecheckHandler());
    buttonRow.add(typecheckButton);
    convert_ = new JButton("toUnicode");
    convert_.addActionListener(new ConvertHandler());
    buttonRow.add(convert_);
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
		  "\u2500\n  function 42 leftassoc ( _ OPERATOR _ )\n\u2029\n",
		  "\\begin{zed}\n  \\function 42 \\leftassoc ( \\varg OPERATOR \\varg )\n\\end{zed}\n",
		  "Operator Template"),
	new ZChar("[G]",
		  "\u2500 [ TYPE ] \u2029\n",
		  "\\begin{zed}\n  [ TYPE ]\n\\end{zed}\n",
		  "Given Sets"),
	new ZChar("Ax",
		  "\u2577\n  DECLS\n|\n  PREDS\n\u2029\n",
		  "\\begin{axdef}\n  DECLS\n\\where\n  PREDS\n\\end{axdef}\n",
		  "Axiomatic Definition"),
	new ZChar("Ax[]",
		  "\u2577\u2550[ TYPE ]\n  DECLS\n|\n  PREDS\n\u2029\n",
		  "\\begin{gendef}[ TYPE ]\n  DECLS\n\\where\n  PREDS\n\\end{gendef}\n",
		  "Generic Axiomatic Definition"),
	new ZChar("::=",
		  "\u2500\n  TYPE ::= NAME | NAME \u27EA TYPE \u27EB\n\u2029\n",
		  "\\begin{zed}\n  TYPE ::= NAME | NAME \\ldata TYPE \\rdata\n\\end{zed}\n",
		  "Freetype Definition"),
	new ZChar("==",
		  "\u2500\n  NAME == EXPR\n\u2029\n",
		  "\\begin{zed}\n  NAME == EXPR\n\\end{zed}\n",
		  "Horizontal Definition"),
	new ZChar("Sch",
		  "\u250C NAME\n  DECLS\n|\n  PREDS\n\u2029\n",
		  "\\begin{schema}{NAME}\n  DECLS\n\\where\n  PREDS\n\\end{schema}\n",
		  "Schema Definition"),
	new ZChar("Sch[]",
		  "\u250C\u2550 NAME [ TYPE ]\n  DECLS\n|\n  PREDS\n\u2029\n",
		  "\\begin{schema}{NAME}[ TYPE ]\n  DECLS\n\\where\n  PREDS\n\\end{schema}\n",
		  "Generic Schema Definition"),
	new ZChar("\u22A2?",
		  "\u2500\n  \u22A2? PRED\n\u2029\n",
		  "\\begin{zed}\n  \\vdash? PRED\n\\end{zed}\n",
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
//	new ZChar("\uD835\uDD3D", "\\finset", "Finite Power Set"),  // U+1D53D
	new ZChar("{", "\\{", "Begin Set"),
	new ZChar("|", "|", "Such That"),
	new ZChar("\u2981", "@", "Returning"),
	new ZChar("}", "\\}", "End Set"),
	new ZChar("\u2205", "\\emptyset", "Empty Set"),
	new ZChar("\u222A", "\\cup", "Union"),
	new ZChar("\u22C3", "\\bigcup", "n-ary Union"),
	new ZChar("\u2229", "\\cap", "Intersection"),
	new ZChar("\u22C2", "\\bigcap", "n-ary Intersection"),
	new ZChar("\u2216", "\\setminus", "Set Subtraction"),
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
	new ZChar("\u2987  \u2988", "\\limg  \\rimg", "Relational Image"),
	new ZChar("\u2197+\u2199", "^{+}", "Transitive closure")
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
	new ZChar("\u2218", "\\circ", "Functional Composition"),
	new ZChar("\u03BB", "\\lambda", "Lambda"),
	new ZChar("\u03BC", "\\mu", "Mu (Choice)")
      },
      { "Sequences",
	new ZChar("\u27E8  \u27E9", "\\langle  \\rangle", "Literal Sequence"),
	new ZChar("\u2040", "\\cat", "Concatenation"),
	new ZChar("\u2040/", "\\dcat", "Distributed Concatenation"),
	new ZChar("\u21BF", "\\extract", "Extract"),
	new ZChar("\u21BE", "\\filter", "Filter"),
	new ZChar("#", "\\#", "Size of a finite set")
      },
      { "Arithmetic",
	new ZChar("\u2124", "\\num", "Integers"),
	new ZChar("\u2115", "\\nat", "Natural Numbers"),
	new ZChar("\uD835\uDD38", "\\arithmos", "All Numbers"),  // U+1D538
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
	new ZChar("\u2989..\u298A", "\u2989 NAME == EXPR \u298A", 
			"\\lblot NAME == EXPR \\rblot", "Literal Binding"),
	new ZChar("\u29F9", "\\hide", "Schema Hiding"),
	new ZChar("\u2A21", "\\project", "Schema Projection"),
	new ZChar("\u2A1F", "\\semi", "Sequential Composition"),
	new ZChar("\u2A20", "\\pipe", "Schema Piping"),
	new ZChar("\u2032", "'", "Prime decoration"),
	new ZChar("\u21981\u2196", "_{1}", "Subscript decoration"),
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

  private Term parse(SectionManager manager)
  {
    try {
      final Buffer buffer = mView.getBuffer();
      if (buffer.isDirty()) {
        try {
          final String message = "Current buffer is unsaved.\n" +
            "Continue with the original on-disk version?";
          int answer =
            JOptionPane.showConfirmDialog(mView,
                                          message,
                                          "CZT Question",
                                          JOptionPane.YES_NO_OPTION);
          if (answer == 1) {
            CztLogger.getLogger(ZCharMap.class).info("Abborting parse.");
            return null;
          }
        }
        catch (HeadlessException exception) {
          final String message = "Current buffer is unsaved.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      Term term = parse(buffer, manager);
      checkTerm(term);
      return term;
    }
    catch (ParseException exception) {
      CztLogger.getLogger(ZCharMap.class).info("Parse error(s) occured.");
      List errors = exception.getErrorList();
      for (Iterator iter = errors.iterator(); iter.hasNext(); ) {
        Object next = iter.next();
        ParseError parseError = (ParseError) next;
        addError(mView.getBuffer().getPath(), parseError.getLine() - 1,
                 parseError.getColumn() - 1, 0, parseError.toString());
      }
      String message = "Z parsing complete, " + computeErrorNumber();
      mView.getStatus().setMessage(message);
    }
    catch (IOException exception) {
      String message = "Input output error: " + exception.getMessage();
      CztLogger.getLogger(ZCharMap.class).warning(message);
      addError(mView.getBuffer().getPath(), 0, 0, 0 , message);
    }
    return null;
  }

  private ErrorSource.Error[] getAllErrors()
  {
    return CommunityZToolsPlugin.errorSource_.getAllErrors();
  }

  private String computeErrorNumber()
  {
    ErrorSource.Error[] errors = getAllErrors();
    int errorNr = 0;
    int warningNr = 0;
    if (errors != null) {
      for (int i = 0; i < errors.length; i++) {
        final int errorType = errors[i].getErrorType();
        if (errorType == ErrorSource.ERROR) {
          errorNr++;
        }
        else if (errorType == ErrorSource.WARNING) {
          warningNr++;
        }
        else {
          final String message = "Unexpected error type " + errorType;
          CztLogger.getLogger(ZCharMap.class).warning(message);
        }
      }
    }
    return errorNr + " error(s), " + warningNr + " warning(s)";
  }

  private Term parse(Buffer buffer, SectionManager manager)
    throws IOException, ParseException
  {
    final String filename = buffer.getPath();
    final Source source = new FileSource(filename);
    source.setEncoding(buffer.getStringProperty("encoding"));
    if (markup.getSelectedIndex() == 0) {
      source.setMarkup(Markup.LATEX);
    }
    else {
      source.setMarkup(Markup.UNICODE);
    }
    final Properties properties = new Properties();
    String propname =
      CommunityZToolsPlugin.PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS;
    String value = 
      jEdit.getBooleanProperty(propname) ? "true" : "false";
    properties.setProperty(PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS,
                           value);
    propname =
      CommunityZToolsPlugin.PROP_SPACE_BEFORE_PUNCTATION;
    value = 
      jEdit.getBooleanProperty(propname) ? "true" : "false";
    properties.setProperty(PROP_ADD_SPACE_BEFORE_PUNCTATION,
                           value);
    propname =
      CommunityZToolsPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    properties.setProperty(PROP_IGNORE_UNKNOWN_LATEX_COMMANDS,
                           value);
    return ParseUtils.parse(source, manager, properties);
  }

  private void checkTerm(Term term)
  {
    if (term instanceof Spec) {
      Spec spec = (Spec) term;
      List sects = spec.getSect();
      final boolean unnamedSectWithoutContent =
        (sects.size() == 2) &&
        (sects.get(0) instanceof NarrSect) &&
        (sects.get(1) instanceof ZSect) &&
        (((ZSect) sects.get(1)).getPara().size() == 0);
      if (unnamedSectWithoutContent) {
        String message = "No Z constructs found.";
        CztLogger.getLogger(ZCharMap.class).warning(message);
        addWarning(message);
      }
    }
    else {
      String message = "Unexpected term " + term.getClass().getName() + ".";
      CztLogger.getLogger(ZCharMap.class).warning(message);
    }
  }

  private void addError(String location,
                        int line,
                        int column,
                        int length,
                        String message)
  {
    addError(ErrorSource.ERROR, location, line, column, length, message);
  }

  private void addError(int errorType,
                        String location,
                        int line,
                        int column,
                        int length,
                        String message)
  {
    if (line < 0) line = 0;
    if (column < 0) column = 0;
    if (length < 0) length = 0;
    DefaultErrorSource.DefaultError error = 
      new DefaultErrorSource.DefaultError(CommunityZToolsPlugin.errorSource_,
                                          errorType,
                                          location,
                                          line,
                                          column,
                                          length,
                                          message);
    CommunityZToolsPlugin.errorSource_.addError(error);
  }
 
  private void addWarning(String msg)
  {
    addError(ErrorSource.WARNING, mView.getBuffer().getPath(), 0, 0, 0, msg);
  }
 
  private void clearErrorList()
  {
    CommunityZToolsPlugin.errorSource_.clear();
  }

  class TypecheckHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      clearErrorList();
      CztLogger.getLogger(ZCharMap.class).info("Typechecking ...");
      try {
	SectionManager manager = new SectionManager();
	Term term = parse(manager);
        if (term != null) {
          List errors = TypeCheckUtils.typecheck(term, manager);
          //print any errors
          for (Iterator iter = errors.iterator(); iter.hasNext(); ) {
            ErrorAnn errorAnn = (ErrorAnn) iter.next();
            addError(mView.getBuffer().getPath(), errorAnn.getLine() - 1,
                     errorAnn.getColumn() - 1, 0, errorAnn.toString());
          }
          final String message =
            "Z typechecking complete, " + computeErrorNumber();
          mView.getStatus().setMessage(message);
          CztLogger.getLogger(ZCharMap.class).info("Done typechecking.");
        }
        else {
          final String message = "Z typechecking aborted.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      catch (Throwable exception) {
        exception.printStackTrace();
        CztLogger.getLogger(ZCharMap.class).info("CZT error occured.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(exception);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
      }
    }
  }

  class ConvertHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      clearErrorList();
      CztLogger.getLogger(ZCharMap.class).info("Converting ...");
      try {
	SectionManager manager = new SectionManager();
	Term term = parse(manager);
        if (term != null) {
          Buffer buffer = jEdit.newFile(mView);
          StringWriter out = new StringWriter();
          if (markup.getSelectedIndex() == 0) {
            buffer.setStringProperty("encoding", "UTF-16");
            PrintUtils.printUnicode(term, out, manager);
          }
          else {
            PrintUtils.printLatex(term, out, manager);
          }
          out.close();
          buffer.insert(0, out.toString());
          CztLogger.getLogger(ZCharMap.class).info("Done converting.");
        }
        else {
          String message = "Z convertion aborted.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      catch (Throwable exception) {
        CztLogger.getLogger(ZCharMap.class).info("CZT error occured.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(message);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
      }
    }
  }

  class XmlHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      clearErrorList();
      try {
	SectionManager manager = new SectionManager();
	Term term = parse(manager);
        if (term != null) {
          net.sourceforge.czt.z.jaxb.JaxbXmlWriter writer =
            new net.sourceforge.czt.z.jaxb.JaxbXmlWriter();
          Buffer buffer = jEdit.newFile(mView);
          buffer.setStringProperty("encoding", "UTF-8");
          StringWriter out = new StringWriter();
          writer.write(term, out);
          out.close();
          buffer.insert(0, out.toString());
        }
        else {
          String message = "Z convertion aborted.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      catch (Throwable exception) {
        CztLogger.getLogger(ZCharMap.class).info("CZT error occured.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(message);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
      }
    }
  }

  class MarkupHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      try {
        if (markup.getSelectedIndex() == 0) {
          convert_.setText("toUnicode");
        }
        else {
          convert_.setText("toLatex");
        }
     }
      catch (Throwable exception) {
        CztLogger.getLogger(ZCharMap.class).info("CZT error occured.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(message);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
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
