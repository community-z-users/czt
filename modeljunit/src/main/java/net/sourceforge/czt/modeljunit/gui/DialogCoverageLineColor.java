
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.GridLayout;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import javax.swing.DefaultComboBoxModel;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.ListCellRenderer;

/*
 * @author Rong Yang date: 28th Nov 2007
 */
public class DialogCoverageLineColor extends JDialog
{
  private static final long serialVersionUID = 1371399697321421718L;

  public static final Color[] LINE_COVERAG_COLOR = {Color.BLACK, Color.RED,
      Color.GREEN, Color.BLUE, Color.GRAY, Color.YELLOW, Color.ORANGE,
      Color.CYAN};

  private static final String[] STR_COVERAGE_NAME = {"State", "Transition",
      "Transition pair", "Action"};

  private JComboBox[] m_comboColorList = new JComboBox[Parameter.NUM_COVERAGE];

  private ComboBoxModel[] m_modelComboBox = new ComboBoxModel[Parameter.NUM_COVERAGE];

  private LineColor[] m_colorLine;

  private JPanel m_panel;

  public DialogCoverageLineColor(Frame owner)
  {
    super(owner, "Color selection dialog", true);
    setDefaultCloseOperation(DISPOSE_ON_CLOSE);
    m_colorLine = new LineColor[LINE_COVERAG_COLOR.length];
    // Create color list according to LINE_COVERAG_COLOR color list
    for (int i = 0; i < LINE_COVERAG_COLOR.length; i++)
      m_colorLine[i] = new LineColor(null, LINE_COVERAG_COLOR[i]);
    // Get current line colors 
    getCurrentLineColors();
    // output 4 debug
    // outputLineColors();

    m_panel = new JPanel();
    GridLayout layout = new GridLayout(0, 2);
    layout.setHgap(5);
    layout.setVgap(5);
    m_panel.setLayout(layout);
    // Create combobox and initialize 
    createComboBoxes();
    for (int i = 0; i < Parameter.NUM_COVERAGE; i++) {
      m_panel.add(new JLabel(STR_COVERAGE_NAME[i]));
      m_panel.add(m_comboColorList[i]);
    }
    getContentPane().add(m_panel);
    pack();
  }

  private void createComboBoxes()
  {
    for (int i = 0; i < Parameter.NUM_COVERAGE; i++) {
      ComboBoxItemRender r = new ComboBoxItemRender(
          getAvailableColorList(STR_COVERAGE_NAME[i]));
      r.setPreferredSize(new Dimension(20, 10));
      m_modelComboBox[i] = new ComboBoxModel(
          getAvailableColorList(STR_COVERAGE_NAME[i]), i);
      m_comboColorList[i] = new JComboBox(m_modelComboBox[i]);

      m_comboColorList[i].addItemListener(new ItemListener()
      {
        public void itemStateChanged(ItemEvent e)
        {
          //check if a new item is selected
          if (e.getStateChange() == 1) {
            selectChangeHandler(e);
          }
        }
      });
      m_comboColorList[i].setRenderer(r);
      m_comboColorList[i].setMaximumRowCount(3);
      m_comboColorList[i].setSelectedIndex(0);
    }
  }

  // Every time user change the line's color
  // This function will be called to update
  // items in combobox
  private void reloadComboBoxes()
  {
    for (int i = 0; i < Parameter.NUM_COVERAGE; i++) {
      Color[] color = getAvailableColorList(STR_COVERAGE_NAME[i]);
      m_modelComboBox[i].removeAllElements();
      for (Color c : color)
        m_modelComboBox[i].addElement(c);
      Color[] c = getAvailableColorList(STR_COVERAGE_NAME[i]);
      ComboBoxItemRender r = new ComboBoxItemRender(c);
      this.m_comboColorList[i].setRenderer(r);
    }
    m_panel.updateUI();
  }

  /** Get color from parameter class
   * "State"  State coverage line color
   * "Transition"  Transition coverage line color
   * "Transition Pair" Transition pair coverage line color
   * "Action"  Action coverage line color
   * */
  private void getCurrentLineColors()
  {
    // Get current coverage line color from Parameter class
    Color[] curColors = Parameter.getCoverageLineColors();
    for (int i = 0; i < Parameter.NUM_COVERAGE; i++) {
      for (int j = 0; j < LINE_COVERAG_COLOR.length; j++)
        if (LINE_COVERAG_COLOR[j].equals(curColors[i]))
          m_colorLine[j].m_strCoverage = STR_COVERAGE_NAME[i];
    }
  }

  /**
   * Two coverage line color are excluding.
   * This function is for calculate which color
   * is available for particular coverage.
   * */
  private Color[] getAvailableColorList(String coverage)
  {
    // Calculate how many colors available
    Color[] availableColor = new Color[LINE_COVERAG_COLOR.length
        - Parameter.NUM_COVERAGE + 1];
    // System.out.println("available line color#: "+availableColor.length);
    int nSelectedColor = 0;
    int nAvailableColorIdx = 0;
    for (int i = 0; i < m_colorLine.length; i++) {
      if (m_colorLine[i].m_strCoverage == null) {
        // System.out.println("Count to: "+i);
        availableColor[nAvailableColorIdx] = m_colorLine[i].m_color;
        nSelectedColor = nAvailableColorIdx;
        nAvailableColorIdx++;
      }
      else if (m_colorLine[i].m_strCoverage != null
          && m_colorLine[i].m_strCoverage.equals(coverage)) {
        availableColor[nAvailableColorIdx] = m_colorLine[i].m_color;

        nAvailableColorIdx++;
      }
    }
    // Put the selected color to the end of the color array
    Color c = availableColor[nSelectedColor];
    availableColor[nSelectedColor] = availableColor[0];
    availableColor[0] = c;
    return availableColor;
  }

  // Output color string for debug
  private void outputLineColors()
  {
    for (LineColor lc : m_colorLine) {
      if (lc.m_strCoverage != null)
        System.out.println(lc.m_color.toString() + ", " + lc.m_strCoverage);
      else
        System.out.println(lc.m_color.toString());
    }
  }


  private class ComboBoxModel extends DefaultComboBoxModel
  {
    private static final long serialVersionUID = 8208933386178935385L;

    DefaultComboBoxModel def;

    private Color[] m_color;

    private int m_nCursor;

    private int m_nID;

    /**
     *  color:  the data that the combobox owns
     *  id:     id of the combobox box
     *          0.State coverage 
     *          1.Transition coverage
     *          2.Transition pair coverage
     *          3.action coverage
     */
    public ComboBoxModel(Color[] color, int id)
    {
      m_nCursor = 0;
      m_nID = id;
      m_color = new Color[color.length];
      for (int i = 0; i < color.length; i++) {
        addElement(color[i]);
        m_color[i] = color[i];
      }
    }

    public int getID()
    {
      return m_nID;
    }

    public void setColor(int idx, Color color)
    {
      m_color[idx] = color;
    }

    // The number of available color is fixed 
    public void addElement(Object color)
    {
      //System.out.println("addElement");
      for (int i = 0; i < m_color.length; i++) {
        if (m_color[i] == null)
          m_color[i] = (Color) color;
      }
    }

    public Object getSelectedItem()
    {
      //System.out.println("getSelectedItem:"+m_color[m_nCursor]+", ID: "+m_nID);
      return m_color[m_nCursor];
    }

    public Object getElementAt(int index)
    {
      // System.out.println("getElementAt:"+m_color[index].toString());
      m_nCursor = index;
      return (Object) m_color[index];
    }

    public int getIndexOf(Object o)
    {
      //System.out.println("getIndexOf");
      for (int i = 0; i < m_color.length; i++) {
        if (m_color[i].getRed() == ((Color) o).getRed()
            && m_color[i].getBlue() == ((Color) o).getBlue()
            && m_color[i].getGreen() == ((Color) o).getGreen()) {
          System.out.println("found" + m_color.toString() + "number: " + i);
          return i;
        }
      }
      return -1;
    }

    public int getSize()
    {
      return m_color.length;
    }

    public void removeElementAt(int index)
    {
      m_color[index] = null;
    }

    public void removeElement(Object o)
    {
      removeElementAt(getIndexOf(o));
    }

    public void removeAllElements()
    {
      m_nCursor = -1;
      for (int i = 0; i < m_color.length; i++)
        m_color[i] = null;
    }

    public void setSelectedItem(Object o)
    {
      //System.out.println("setSelectedItem");
      m_nCursor = getIndexOf(o);
    }
  }


  private class ComboBoxItemRender extends JLabel implements ListCellRenderer
  {
    private static final long serialVersionUID = -7309237550133230366L;

    private Color[] m_color;

    private Color m_colorCell;

    public ComboBoxItemRender(Color[] color)
    {
      setOpaque(true);
      setHorizontalAlignment(CENTER);
      setVerticalAlignment(CENTER);
      m_color = color;
    }

    @Override
    public Component getListCellRendererComponent(JList list, Object value,
        int index, boolean isSelected, boolean cellHasFocus)
    {
      // int selectedIdx = ((Integer)value).intValue();
      this.setPreferredSize(new Dimension(16, 32));
      this.setBackground(Color.WHITE);

      if (isSelected) {
        setBackground(list.getSelectionBackground());
        setForeground(list.getSelectionForeground());
      }
      else {
        //setBackground(list.getBackground());
        setBackground(Color.WHITE);
        setForeground(list.getForeground());
      }

      if (index >= 0) {
        m_colorCell = (Color) value;
        // System.out.println("color is:"+((Color)value).toString());
      }
      if (index == -1) {
        m_colorCell = (Color) value;
      }
      return this;
    }

    @Override
    public void paint(Graphics g)
    {
      super.paint(g);
      g.setColor(m_colorCell);
      // System.out.println(getWidth()+", "+getHeight());
      g.fillRect(6, 6, this.getWidth() - 12, this.getHeight() - 10);
    }
  }

  private void selectChangeHandler(ItemEvent e)
  {
    Color[] colors = Parameter.getCoverageLineColors();
    if (e.getSource() == m_comboColorList[0]) {
      Color c = (Color) m_comboColorList[0].getSelectedItem();
      colors[0] = c;
    }
    else if (e.getSource() == m_comboColorList[1]) {
      Color c = (Color) m_comboColorList[1].getSelectedItem();
      colors[1] = c;
      System.out.println("---1------>" + c.toString());
    }
    else if (e.getSource() == m_comboColorList[2]) {
      Color c = (Color) m_comboColorList[2].getSelectedItem();
      colors[2] = c;
      System.out.println("---2------>" + c.toString());
    }
    else if (e.getSource() == m_comboColorList[3]) {
      Color c = (Color) m_comboColorList[3].getSelectedItem();
      colors[3] = c;
      System.out.println("---3------>" + c.toString());
    }
    Parameter.setCoverageLineColors(colors);
    reloadComboBoxes();
  }
}
