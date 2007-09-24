
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.lang.reflect.InvocationTargetException;

import javax.swing.JPanel;
import net.sourceforge.czt.modeljunit.Tester;

public class OptionPanelAdapter extends JPanel implements IAlgorithmParameter
{
  /**
   * Serial version UID
   */
  private static final long serialVersionUID = 1528786500050772844L;

  protected Tester m_tester;
  public Tester GetTester()
  {
    return m_tester;
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

  public void saveParameters(BufferedWriter bufWriter)
  {
  }

  public String generateImportLab()
  {
    return null;
  }

  public void runAlgorithm(){}
}
