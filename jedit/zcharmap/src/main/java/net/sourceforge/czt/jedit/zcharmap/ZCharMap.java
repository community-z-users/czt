/*
 * ZCharMap.java
 * Copyright (C) 2003, 2004, 2006 Petra Malik
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
package net.sourceforge.czt.jedit.zcharmap;

import java.awt.event.*;
import java.awt.*;
import java.io.*;
import java.net.URL;
import java.util.List;
import javax.swing.event.*;
import javax.swing.table.*;
import javax.swing.*;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.gjt.sp.jedit.*;
import org.gjt.sp.jedit.msg.*;
import java.util.ArrayList;

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
  implements EBComponent
{
  //############################################################
  //##################### MEMBER VARIABLES #####################
  //############################################################

  /**
	 * 
	 */
	private static final long serialVersionUID = -3854731389073765118L;

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
  private TableModel circusTableModel_;
  private TableModel zevesTableModel_;

  /**
   * The status bar label.
   */
  private JLabel status;

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
    EditBus.addToBus(this);
    mView = view;

    org.gjt.sp.jedit.textarea.TextAreaPainter textAreaPainter =
      mView.getTextArea().getPainter();
    renderingHints = textAreaPainter.getRenderingHints();

    zTableModel_ = new ZCharTable(getClass().getResource("/ZTable.xml"));
    objectZTableModel_ =
      new ZCharTable(getClass().getResource("/ObjectZTable.xml"));
    circusTableModel_ = new ZCharTable(getClass().getResource("/CircusTable.xml"));
    zevesTableModel_ = new ZCharTable(getClass().getResource("/ZEvesTable.xml"));
    mTable = new JTable();
    setTableModel();    
    
    JScrollPane scrollPane = new JScrollPane(mTable);
    mTable.setPreferredScrollableViewportSize(new Dimension(300, 70));
    mTable.setFillsViewportHeight(true);    
    mTable.setFont(view.getTextArea().getPainter().getFont());    
    mTable.setRowHeight(view.getTextArea().getPainter().getFont().getSize()+4);
    mTable.setFocusable(false);
    mTable.setDefaultRenderer(ZChar.class, new StringRenderer(true));
    mTable.setDefaultRenderer(String.class, new StringRenderer(false));
    mTable.setRowSelectionAllowed(false);
    mTable.setColumnSelectionAllowed(false);
    mTable.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
    mTable.addMouseListener(new MouseHandler());
    mTable.addMouseMotionListener(new MouseHandler());
    
    add(BorderLayout.CENTER, scrollPane);
    
    status = new StatusRenderer(" ");
    status.setFont(view.getTextArea().getPainter().getFont());
    add(BorderLayout.SOUTH,status);
    setFocusable(false);
  }

  //############################################################
  //###################### METHODS #############################
  //############################################################

  @Override
  public void handleMessage(EBMessage message)
  {
    if (message instanceof EditPaneUpdate) {
      EditPaneUpdate editPaneUpdate = (EditPaneUpdate) message;
      if (editPaneUpdate.getWhat() == EditPaneUpdate.BUFFER_CHANGED) {
        setTableModel();
        mTable.repaint();
      }
    }
    if (message instanceof ViewUpdate) {
      ViewUpdate viewUpdate = (ViewUpdate) message;
      if (viewUpdate.getWhat() == ViewUpdate.EDIT_PANE_CHANGED) {
        setTableModel();
        mTable.repaint();
      }
    }
    else if (message instanceof BufferUpdate) {
      BufferUpdate bufferUpdate = (BufferUpdate) message;
      if (bufferUpdate.getWhat() == BufferUpdate.PROPERTIES_CHANGED) {
        setTableModel();
        mTable.repaint();
      }
    }
  }

  private static final int MIN_STR_WIDTH = 50;
  private final List<String> widestCollumn = new ArrayList<String>();
//  private static int check = 1;
  
  private void setTableModel()
  {
    Mode mode = mView.getBuffer().getMode();    
    if (mode != null) {
      if  ("oz".equals(mode.toString()) || "ozlatex".equals(mode.toString())) {        
        mTable.setModel(objectZTableModel_);
      } else if ("circus".equals(mode.toString()) || "circuslatex".equals(mode.toString())) {
        mTable.setModel(circusTableModel_);
      } else if ("zeves".equals(mode.toString()) || "zeveslatex".equals(mode.toString())) {
        mTable.setModel(zevesTableModel_); 
      } else {
        mTable.setModel(zTableModel_);
      }
    } else {
      mTable.setModel(zTableModel_);
    }
    /*
    FileWriter fw;
    try
    {
      fw = new FileWriter("c:\\temp\\zcharmap3.txt");      
      fw.write(check + "-getTable: " + widestCollumn.toString());
      fw.close();
    } catch (IOException ex)
    {      
      ex.printStackTrace();
    }
     */    
    //check++;
    FontMetrics fm = mView.getFontMetrics(mView.getTextArea().getPainter().getFont());
    for(int colIdx = 0; colIdx < mTable.getColumnModel().getColumnCount(); colIdx++) {
      int strWidth = fm.stringWidth(widestCollumn.get(colIdx));
      mTable.getColumnModel().getColumn(colIdx).setMinWidth(MIN_STR_WIDTH);
      mTable.getColumnModel().getColumn(colIdx).setMaxWidth(strWidth * 2);
      mTable.getColumnModel().getColumn(colIdx).setPreferredWidth(strWidth);
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
	 * 
	 */
	private static final long serialVersionUID = 207544765485161935L;
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
      CztXmlHandler handler = new CztXmlHandler();

      try {
    	InputStream stream = url.openStream();

        try {
          SAXParserFactory factory = SAXParserFactory.newInstance();
          SAXParser saxParser = factory.newSAXParser();
  
          saxParser.parse(stream, handler);
        } finally {
          stream.close();
        }
      }
      catch (Exception e) {
    	throw new RuntimeException(e);
      }
    	
      List<List<Object>> lists = handler.getList();
      int maxsize = 0;
      for (List<Object> list : lists) {
        int size = list.size();
        if (size > maxsize) maxsize = size;
      }
      // row/col
      Object[][] result = new Object[lists.size()][maxsize];
      widestCollumn.clear();
      for(int k = 0; k < maxsize; k++) {
        widestCollumn.add("");
      }
      int i = 0;
      for (List<Object> list : lists) {
        int j = 0;
        for (Object elem : list) {
          result[i][j] = elem;
          if (elem.toString().length() > widestCollumn.get(j).length()) {
            widestCollumn.add(j, elem.toString());
          }
          j++;
        }
        i++;
      }
      return result;
    }

    /**
     * Returns the maximum length of all the rows.
     *
     * @return the number of columns in this table.
     */
    @Override
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
    @Override
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
    @Override
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
    @Override
    public Class<?> getColumnClass(int col)
    {
      if (col==0) return String.class;
      return ZChar.class;
    }

    /**
     * Returns <code>null</code> regardless of the column number.
     *
     * @return <code>null</code>
     */
    @Override
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
    @Override
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
    @Override
    public void mouseClicked(MouseEvent event)
    {
      Point p = event.getPoint();
      int row = mTable.rowAtPoint(p);
      int col = mTable.columnAtPoint(p);
      if(row == -1 || col == -1 || col == 0) {
	status.setText(" ");
      } else {
	ZChar zchar = (ZChar) mTable.getModel().getValueAt(row,col);
	if (isLatex()) {
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
    @Override
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
    @Override
    public void mouseExited(MouseEvent event)
    {
      status.setText(" ");
    }
  }

  private boolean isLatex()
  {
    return mView.getBuffer().getMode().toString().contains("latex");
  }

  /**
   * A string renderer which centers the given string onto a JLabel.
   */
  class StringRenderer extends DefaultTableCellRenderer {
    /**
	 * 
	 */
	private static final long serialVersionUID = -7753366536461217359L;

	public StringRenderer(boolean centered)
    {
      super();
      setFont(mView.getTextArea().getPainter().getFont());
      if (centered) {
	setHorizontalAlignment(CENTER);
	setVerticalAlignment(CENTER);
      }
    }

    @Override
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

    @Override
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
    /**
	 * 
	 */
	private static final long serialVersionUID = 3835501190046105676L;

	public StatusRenderer(String string)
    {
      super(string);
      setFont(mView.getTextArea().getPainter().getFont());
    }

    @Override
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
