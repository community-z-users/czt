
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.lang.reflect.InvocationTargetException;

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
  
  protected Tester m_tester;
  
  public Tester getTester()
  {
    return m_tester;
  }
  
  public OptionPanelAdapter(String name, String explain, String imgPath)
  {
    m_strNameOfAlgorithm = name;
    m_strExplanation = explain;
    //m_imgIcon = new ImageIcon(getClass().getResource("icon.gif"));
  }
  
  public String generateCode()
  {
    return null;
  }

  public void initialize()
  {
  }

  public void loadParameters(BufferedReader bufReader)
  {
  }

  public void saveParameters(BufferedWriter bufWriter){}

  public String generateImportLab()
  {
    return null;
  }

  public void runAlgorithm(){}
  
  public String getAlgorithmName()
  {
    return m_strNameOfAlgorithm;
  }

  public String getExplanation()
  {
    return m_strExplanation;
  }
}
