
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.lang.reflect.InvocationTargetException;

import javax.swing.*;

import net.sourceforge.czt.modeljunit.ModelTestCase;
import net.sourceforge.czt.modeljunit.Tester;

/**
 * AlgorithmPanel.java
 *
 * @author rong
 * ID : 1005450
 * 30th Jl 2007
 * */
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

  public void initialize()
  {
    m_panelOption.initialize();
  }

  public Tester getTester()
  {
    return m_panelOption.getTester();
  }
  
  public void loadParameters(BufferedReader bufReader)
  {
    m_panelOption.loadParameters(bufReader);
  }

  public void saveParameters(BufferedWriter bufWriter)
  {
    m_panelOption.saveParameters(bufWriter);
  }

  public String generateImportLab()
  {
    return m_panelOption.generateImportLab();
  }

  public void runAlgorithm()
  {
    m_panelOption.runAlgorithm();
  }
}
