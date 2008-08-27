
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;

import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JPanel;
import javax.swing.border.Border;

import net.sourceforge.czt.modeljunit.Tester;

public class OptionPanelAdapter extends JPanel implements IAlgorithmParameter
{
  /**
   * Serial version UID
   */
  private static final long serialVersionUID = 1528786500050772844L;

  private String m_strNameOfAlgorithm;

  private String m_strExplanation;

  private ImageIcon m_imgIcon;

  /** 
   * The array of tester object
   * Using array because we need to separate several tester for different panel.
   * 0. For automatically run testing.
   * 1. For manually run testing.
   **/
  protected Tester[] m_tester = new Tester[2];

  public Tester getTester(int idx)
  {
    return m_tester[idx];
  }

  public OptionPanelAdapter(String name, String explain, String imgPath)
  {
    m_strNameOfAlgorithm = name;
    m_strExplanation = explain;
    Border edge = BorderFactory.createLineBorder(Color.WHITE);
    this.setBorder(BorderFactory.createTitledBorder(edge, name+" Parameters"));
    //m_imgIcon = new ImageIcon(getClass().getResource("icon.gif"));
  }

  @Override
  public String generateCode()
  {
    return null;
  }

  @Override
  public void initialize(int idx)
  {
  }

  public String generateImportLab()
  {
    return null;
  }

  @Override
  public void runAlgorithm(int idx)
  {
  }

  public String getAlgorithmName()
  {
    return m_strNameOfAlgorithm;
  }

  public String getExplanation()
  {
    return m_strExplanation;
  }
}
