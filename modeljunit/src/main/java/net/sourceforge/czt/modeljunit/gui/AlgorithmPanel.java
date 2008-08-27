
package net.sourceforge.czt.modeljunit.gui;

import javax.swing.ImageIcon;
import javax.swing.JPanel;

import net.sourceforge.czt.modeljunit.Tester;

/*
 * AlgorithmPanel.java
 * @author rong ID : 1005450 30th Jul 2007
 */
public class AlgorithmPanel extends JPanel implements IAlgorithmParameter
{
  private static final long serialVersionUID = -8482380073303577774L;

  private String m_strNameOfAlgorithm;

  private String m_strExplanation;

  private ImageIcon m_imgIcon;

  private OptionPanelAdapter m_panelOption;

  public AlgorithmPanel(String name, String explain, String imgPath)
  {
    m_strNameOfAlgorithm = name;
    m_strExplanation = explain;
    //m_imgIcon = new ImageIcon(getClass().getResource("icon.gif"));
  }

  public String getAlgorithmName()
  {
    return m_strNameOfAlgorithm;
  }

  public String getExplanation()
  {
    return m_strExplanation;
  }

  public void setOptionPanel(OptionPanelAdapter panel)
  {
    m_panelOption = panel;
  }

  public JPanel getOptionPanel()
  {
    return m_panelOption;
  }

  public String generateCode()
  {
    return m_panelOption.generateCode();
  }

  public void initialize(int idx)
  {
    m_panelOption.initialize(idx);
  }

  public Tester getTester(int idx)
  {
    return m_panelOption.getTester(idx);
  }

  public String generateImportLab()
  {
    return m_panelOption.generateImportLab();
  }

  public void runAlgorithm(int idx)
  {
    m_panelOption.runAlgorithm(idx);
  }
}
