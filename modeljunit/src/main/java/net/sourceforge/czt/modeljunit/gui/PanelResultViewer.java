
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Dimension;
import java.util.Vector;
import javax.swing.*;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.JTableHeader;
import javax.swing.table.TableColumn;

public class PanelResultViewer extends JPanel  
{

  /**
   * 
   */
  private static final long serialVersionUID = -6522938608020451281L;


  class ColumnInformation
  {
    public String m_title;

    public int m_width;

    public int m_alignment;

    public ColumnInformation(String title, int width, int alignment)
    {
      m_title = title;
      m_width = width;
      m_alignment = alignment;
    }
  }


  class ResultTableModelInstance extends AbstractTableModel
  {
    /**
     * 
     */
    private static final long serialVersionUID = 3369812997489556322L;

    public final ColumnInformation m_columns[] = {
        new ColumnInformation("Type", 30, JLabel.LEFT),
        new ColumnInformation("Class name", 60, JLabel.LEFT),
        new ColumnInformation("Description", 100, JLabel.RIGHT),
        new ColumnInformation("Location", 60, JLabel.RIGHT),
        new ColumnInformation("Path", 60, JLabel.RIGHT)};

    protected Vector<ResultDetails> m_vector;

    public ResultTableModelInstance()
    {
      m_vector = new Vector<ResultDetails>();
      clearData();
    }

    public void clearData()
    {
      m_vector.removeAllElements();
    }

    public void addData(ResultDetails rd)
    {
      m_vector.add(rd);
    }

    @Override
    public int getColumnCount()
    {
      return m_columns.length;
    }

    @Override
    public int getRowCount()
    {
      return m_vector == null ? 0 : m_vector.size();
    }

    @Override
    public String getColumnName(int col)
    {
      return m_columns[col].m_title;
    }

    @Override
    public Object getValueAt(int rowIndex, int columnIndex)
    {
      if (rowIndex < 0 || rowIndex >= getRowCount())
        return null;
      ResultDetails row = m_vector.get(rowIndex);
      switch (columnIndex) {
        case 0 :
          return row.strType;
        case 1 :
          return row.strName;
        case 2 :
          return row.strDescription;
        case 3 :
          return row.strLocation;
        case 4 :
          return row.strPath;
      }
      return null;
    }

    @Override
    public boolean isCellEditable(int nRow, int nCol)
    {
      return false;
    }

    public String getTitle()
    {
      return "Compile result table";
    }

  }

  private static PanelResultViewer m_panelRV;

  // Minimum height of the table and text area 
  private final int MIN_HIEHGT = 160;
  private final int INITIAL_WIDTH = 300;
  private JTable m_table;
  private ResultTableModelInstance m_columeModel;
  // Display the test running information 
  private JTextArea m_txtOutput;
  // Scroll pane
  JScrollPane m_scrollTable;
  JScrollPane m_scrollTextArea;
  // Split pane
  JSplitPane m_splitPane; 
  
  

  public ResultTableModelInstance getTableModel()
  {
    return m_columeModel;
  }

  public static PanelResultViewer createResultViewer()
  {
    if (m_panelRV == null)
      m_panelRV = new PanelResultViewer();
    return m_panelRV;
  }

  private PanelResultViewer()
  {
    m_table = new JTable();
    m_table.setAutoCreateColumnsFromModel(false);
    m_columeModel = new ResultTableModelInstance();
    m_table.setModel(m_columeModel);

    for (int i = 0; i < m_columeModel.getColumnCount(); i++) {
      DefaultTableCellRenderer render = new DefaultTableCellRenderer();
      render.setHorizontalAlignment(m_columeModel.m_columns[i].m_alignment);
      render.setText(m_columeModel.m_columns[i].m_title);
      TableColumn column = new TableColumn(i,
          m_columeModel.m_columns[i].m_width, render, null);
      m_table.addColumn(column);
    }

    JTableHeader header = m_table.getTableHeader();
    header.setUpdateTableInRealTime(false);

    // -------------------- Set up the split pane ------------------
    // Scroll for compile table
    m_scrollTable = new JScrollPane(m_table);
    m_table.setFillsViewportHeight(true);
    m_scrollTable.getViewport().setBackground(m_table.getBackground());
    m_scrollTable.getViewport().add(m_table);

    // Scroll pane for text area
    m_txtOutput = new JTextArea();
    m_txtOutput.setEditable(false);
    //m_txtOutput.setPreferredSize(new Dimension(INITIAL_WIDTH,MIN_HIEHGT));
    m_scrollTextArea = new JScrollPane(m_txtOutput);
    m_scrollTextArea.getViewport().setBackground(m_txtOutput.getBackground());
    m_scrollTextArea.getViewport().add(m_txtOutput);

    m_splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, m_scrollTable, m_scrollTextArea);
    m_splitPane.setOneTouchExpandable(true);
    m_splitPane.setDividerLocation(MIN_HIEHGT);
    //Provide minimum sizes for the two components in the split pane.
    Dimension minimumSize = new Dimension(INITIAL_WIDTH, MIN_HIEHGT);
    m_scrollTable.setMinimumSize(minimumSize);
    m_scrollTextArea.setMinimumSize(minimumSize);

    add(m_splitPane);
  }

  public void updateResult()
  {

  }
  public void resetRunTimeInformation()
  {
    m_txtOutput.setText("");
  }
  
  public void updateRunTimeInformation(String str)
  {
    m_txtOutput.append(str);
  }
  
  public void resizeScrollPanes(Dimension dim)
  {
    m_splitPane.setPreferredSize(dim);
  }
 }
