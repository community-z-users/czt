package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.GridLayout;
import java.util.TreeMap;

import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.ListCellRenderer;

public class DialogCoverageLineColor extends JDialog
{
  private JComboBox[] m_combColorList = new JComboBox[4];
  
  private Color[] m_color = Parameter.getCoverageColors();
  private TreeMap<Color,String> m_mapColor = Parameter.getLineColorList();
  private Color[] m_colorAvailableColor;
  
  public DialogCoverageLineColor(Frame owner)
  {
    super(owner, "Color selection dialog", true);

    JPanel p = new JPanel();
    GridLayout layout = new GridLayout(0,2);
    layout.setHgap(5);
    layout.setVgap(5);
    p.setLayout(layout);
    
    ComboBoxItemRender renderer = new ComboBoxItemRender("AAA",Color.GREEN);
    renderer.setPreferredSize(new Dimension(20,10));
    
    availableColor();
    m_combColorList[0] = new JComboBox(getAvailableColorList(m_color[0]));
    m_combColorList[0].setMaximumRowCount(3);
    p.add(new JLabel("State coverage"));
    p.add(m_combColorList[0]);
    
    m_combColorList[1] = new JComboBox(getAvailableColorList(m_color[1]));
    m_combColorList[1].setMaximumRowCount(3);
    p.add(new JLabel("Transition coverage"));
    p.add(m_combColorList[1]);
    
    m_combColorList[2] = new JComboBox(getAvailableColorList(m_color[2]));
    m_combColorList[2].setMaximumRowCount(3);
    p.add(new JLabel("Transition pair coverage"));
    p.add(m_combColorList[2]);
    
    m_combColorList[3] = new JComboBox(getAvailableColorList(m_color[3]));
    m_combColorList[3].setMaximumRowCount(3);
    p.add(new JLabel("Action coverage"));
    p.add(m_combColorList[3]);
    
    getContentPane().add(p);
    pack();
  }
  
  private void availableColor()
  {
    int size = m_mapColor.size();
    // Total number of color in list - 4 color already used by coverage.
    // To calculate how many color available currently.
    m_colorAvailableColor = new Color[size-4];
    int k = 0;
    for(int i=0;i<Parameter.LINE_COVERAG_COLOR.length;i++)
    {
      for(int j=0;j<m_color.length;j++)
      {
        if(Parameter.LINE_COVERAG_COLOR[i].equals(m_color[j]))
          continue;
      }
      m_colorAvailableColor[k] = Parameter.LINE_COVERAG_COLOR[i];
      System.out.println(m_colorAvailableColor[k]);
      k++;
    }
  }
  
  private String[] getAvailableColorList(Color curColor)
  {
    return null;
  }
  private class ComboBoxItemRender extends JLabel
    implements ListCellRenderer
  {
    private String m_strColor;
    private Color m_color;
    
    public ComboBoxItemRender(String strColor, Color color)
    {
      setOpaque(true);
      setHorizontalAlignment(CENTER);
      setVerticalAlignment(CENTER);
      m_strColor = strColor;
      m_color = color;
    }
    
    @Override
    public Component getListCellRendererComponent(JList list, Object value,
        int index, boolean isSelected, boolean cellHasFocus)
    {
      int selectedIdx = ((Integer)value).intValue();
      if(isSelected)
      {
        if (isSelected) {
          setBackground(list.getSelectionBackground());
          setForeground(list.getSelectionForeground());
        } else {
          setBackground(list.getBackground());
          setForeground(list.getForeground());
        }
      }
      setFont(list.getFont());
      setText(m_strColor);
      return this;
    }
  }
}
