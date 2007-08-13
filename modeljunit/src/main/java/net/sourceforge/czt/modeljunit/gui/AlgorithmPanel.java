
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import javax.swing.*;

public class AlgorithmPanel extends JPanel implements IAlgorithmParameter
{
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

  public boolean hasError()
  {
    return m_panelOption.hasError();
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

  @Override
  public String generateCode()
  {
    return m_panelOption.generateCode();
  }

  @Override
  public void initialize()
  {
    m_panelOption.initialize();
  }

  @Override
  public void loadParameters(BufferedReader bufReader)
  {
    m_panelOption.loadParameters(bufReader);
  }

  @Override
  public void saveParameters(BufferedWriter bufWriter)
  {
    m_panelOption.saveParameters(bufWriter);
  }

  @Override
  public String generateImportLab()
  {
    return m_panelOption.generateImportLab();
  }
}
