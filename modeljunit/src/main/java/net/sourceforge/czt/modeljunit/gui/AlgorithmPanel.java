
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.lang.reflect.InvocationTargetException;

import javax.swing.*;

import net.sourceforge.czt.modeljunit.ModelTestCase;

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

  public String generateCode()
  {
    return m_panelOption.generateCode();
  }

  public void initialize()
  {
    m_panelOption.initialize();
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

  public ModelTestCase runAlgorithm()
  {
    ModelTestCase testcase = null;
    try {
      testcase = m_panelOption.runAlgorithm();
    }
    catch (InstantiationException e) {
      e.printStackTrace();
    }
    catch (IllegalAccessException e) {
      e.printStackTrace();
    }
    catch (SecurityException e) {
      e.printStackTrace();
    }
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
    catch (NoSuchMethodException e) {
      e.printStackTrace();
    }
    catch (InvocationTargetException e) {
      e.printStackTrace();
    }
    return testcase;
  }
}
