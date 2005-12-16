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
import java.io.*;
import java.net.URL;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;
import javax.swing.event.*;
import javax.swing.table.*;
import javax.swing.*;

import org.gjt.sp.jedit.*;
import com.microstar.xml.*;
import errorlist.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlWriter;
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
  private TableModel zTableModel_;
  private TableModel objectZTableModel_;

  /**
   * The status bar label.
   */
  private JLabel status;

  private JComboBox extension;

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
    extension =
      new JComboBox(new String[] { "Standard Z", "Object-Z" });
    extension.addActionListener(new ExtensionHandler());
    buttonRow.add(extension);
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

    zTableModel_ = new ZCharTable(getClass().getResource("/ZTable.xml"));
    objectZTableModel_ =
      new ZCharTable(getClass().getResource("/ObjectZTable.xml"));
    mTable = new JTable();
    setTableModel();
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
  //###################### METHODS #############################
  //############################################################

  public boolean isStandardZ()
  {
    return extension.getSelectedIndex() == 0;
  }

  public boolean isObjectZ()
  {
    return extension.getSelectedIndex() == 1;
  }

  private void setTableModel()
  {
    if (isObjectZ()) {
      mTable.setModel(objectZTableModel_);
    }
    else {
      mTable.setModel(zTableModel_);
    }
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
    private final Object[][] mTableArray;

    public ZCharTable(URL url)
    {
      mTableArray = getTable(url);
    }

    private Object[][] getTable(URL url)
    {
      try {
        InputStream stream = url.openStream();
        XmlParser parser = new XmlParser();
        CztXmlHandler handler = new CztXmlHandler();
        parser.setHandler(handler);
        parser.parse(null, null, stream, null);
        List<List<Object>> lists = handler.getList();
        int maxsize = 0;
        for (List<Object> list : lists) {
          int size = list.size();
          if (size > maxsize) maxsize = size;
        }
        Object[][] result = new Object[lists.size()][maxsize];
        int i = 0;
        for (List<Object> list : lists) {
          int j = 0;
          for (Object elem : list) {
            result[i][j] = elem;
            j++;
          }
          i++;
        }
        return result;
      }
      catch (Exception e) {
        throw new RuntimeException(e);
      }
    }

    /**
     * Returns the maximum length of all the rows.
     *
     * @return the number of columns in this table.
     */
    public int getColumnCount()
    {
      int erg = 0;
      for(int i=0; i < mTableArray.length; i++) {
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
            CztLogger.getLogger(ZCharMap.class).info("Aborting parse.");
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
    catch (CommandException exception) {
      Throwable cause = exception.getCause();
      if (cause instanceof ParseException) {
        CztLogger.getLogger(ZCharMap.class).info("Parse error(s) occurred.");
        List errors = ((ParseException) cause).getErrorList();
        for (Iterator iter = errors.iterator(); iter.hasNext(); ) {
          Object next = iter.next();
          ParseError parseError = (ParseError) next;
          addError(mView.getBuffer().getPath(), parseError.getLine() - 1,
                   parseError.getColumn() - 1, 0, parseError.getMessage());
        }
        String message = "Z parsing complete, " + computeErrorNumber();
        mView.getStatus().setMessage(message);
      }
      else if (cause instanceof IOException) {
        String message = "Input output error: " + cause.getMessage();
        CztLogger.getLogger(ZCharMap.class).warning(message);
        addError(mView.getBuffer().getPath(), 0, 0, 0 , message);
      }
      else {
        String message = "Error while parsing: " + exception.getMessage();
        CztLogger.getLogger(ZCharMap.class).warning(message);
        addError(mView.getBuffer().getPath(), 0, 0, 0 , message);
      }
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
    throws CommandException
  {
    final String filename = buffer.getPath();
    final Source source = new FileSource(filename);
    source.setEncoding(buffer.getStringProperty("encoding"));
    source.setMarkup(getMarkup());
    final String name = "jedit://buffer";
    manager.put(new Key(name, Source.class), source);
    return (Term) manager.get(new Key(name, Spec.class));
  }

  private Markup getMarkup()
  {
    if (markup.getSelectedIndex() == 0) {
      return Markup.LATEX;
    }
    else {
      return Markup.UNICODE;
    }
  }

  private Properties getParseProperties()
  {
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
    return properties;
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

  /**
   * Creates a new section manager and sets the default commands
   * depending on the extension selected by the user.
   */
  private SectionManager getSectionManager()
  {
    if (isObjectZ()) {
      SectionManager manager = new SectionManager();
      Command parseCommand =
          net.sourceforge.czt.parser.oz.ParseUtils.getCommand();
      manager.putCommand(Spec.class, parseCommand);
      manager.putCommand(ZSect.class, parseCommand);
      return manager;
    }
    else {
      return new SectionManager();
    }
  }

  private List<? extends ErrorAnn> typecheck(Term term, SectionManager manager)
  {
    if (isObjectZ()) {
      return net.sourceforge.czt.typecheck.oz.TypeCheckUtils.typecheck(
        term, manager);
    }
    else {
      return TypeCheckUtils.typecheck(term, manager);
    }
  }

  class TypecheckHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      clearErrorList();
      CztLogger.getLogger(ZCharMap.class).info("Typechecking ...");
      try {
	SectionManager manager = getSectionManager();
        Term term = parse(manager);
        if (term != null) {
          List<? extends ErrorAnn> errors = typecheck(term, manager);
          printErrors(errors);
          CztLogger.getLogger(ZCharMap.class).info("Done typechecking.");
        }
        else {
          final String message = "Z typechecking aborted.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      catch (Throwable exception) {
        exception.printStackTrace();
        CztLogger.getLogger(ZCharMap.class).info("CZT error occurred.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(exception);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
      }
    }

    private void printErrors(List<? extends ErrorAnn> errors)
    {
      for (ErrorAnn errorAnn : errors) {
        addError(mView.getBuffer().getPath(), errorAnn.getLine() - 1,
                 errorAnn.getColumn() - 1, 0, errorAnn.toString());
      }
      String message = "Z typechecking complete, " + computeErrorNumber();
      mView.getStatus().setMessage(message);
    }
  }

  class ConvertHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      clearErrorList();
      CztLogger.getLogger(ZCharMap.class).info("Converting ...");
      try {
	SectionManager manager = getSectionManager();
	Term term = parse(manager);
        if (term != null) {
          Buffer buffer = jEdit.newFile(mView);
          StringWriter out = new StringWriter();
          if (markup.getSelectedIndex() == 0) {
            buffer.setStringProperty("encoding", "UTF-16");
            printUnicode(term, out, manager);
          }
          else {
            printLatex(term, out, manager);
          }
          out.close();
          buffer.insert(0, out.toString());
          CztLogger.getLogger(ZCharMap.class).info("Done converting.");
        }
        else {
          String message = "Z conversion aborted.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      catch (Throwable exception) {
        CztLogger.getLogger(ZCharMap.class).info("CZT error occurred.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(message);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
      }
    }

    private void printUnicode(Term term,
                              StringWriter out,
                              SectionManager manager)
    {
      if (isObjectZ()) {
        net.sourceforge.czt.print.oz.PrintUtils.printUnicode(term,
                                                             out,
                                                             manager);
      }
      else {
        PrintUtils.printUnicode(term, out, manager);
      }
    }

    private void printLatex(Term term,
                            StringWriter out,
                            SectionManager manager)
    {
      if (isObjectZ()) {
        net.sourceforge.czt.print.oz.PrintUtils.printLatex(term,
                                                           out,
                                                           manager);
      }
      else {
        PrintUtils.printLatex(term, out, manager);
      }
    }
  }

  class XmlHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      clearErrorList();
      try {
	SectionManager manager = getSectionManager();
	Term term = parse(manager);
        if (term != null) {
          XmlWriter writer = getXmlWriter();
          Buffer buffer = jEdit.newFile(mView);
          buffer.setStringProperty("encoding", "UTF-8");
          StringWriter out = new StringWriter();
          writer.write(term, out);
          out.close();
          buffer.insert(0, out.toString());
        }
        else {
          String message = "Z conversion aborted.";
          CztLogger.getLogger(ZCharMap.class).info(message);
        }
      }
      catch (Throwable exception) {
        CztLogger.getLogger(ZCharMap.class).info("CZT error occurred.");
        String message = "Caught " + exception.getClass().getName() + ": " +
          exception.getMessage();
	System.err.println(message);
        exception.printStackTrace(System.err);
        addError(mView.getBuffer().getPath(), 0, 0, 0, message);
      }
    }

    private XmlWriter getXmlWriter()
    {
      if (isObjectZ()) {
        return new net.sourceforge.czt.oz.jaxb.JaxbXmlWriter();
      }
      else {
        return new net.sourceforge.czt.z.jaxb.JaxbXmlWriter();
      }
    }
  }

  class ExtensionHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      setTableModel();
      mTable.repaint();
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
        CztLogger.getLogger(ZCharMap.class).info("CZT error occurred.");
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
      if (zchar == null) setText("");
      else setText(zchar.toString());
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
