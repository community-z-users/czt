
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.lang.reflect.InvocationTargetException;

import javax.swing.JPanel;

import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.ModelTestCase;

public class OptionPanelAdapter extends JPanel implements IAlgorithmParameter
{

  /**
   * Serial version UID
   */
  private static final long serialVersionUID = 1528786500050772844L;

  protected boolean m_bHasError;
  
  public boolean hasError()
  { return m_bHasError; }
  
  @Override
  public String generateCode()
  {
    return null;
  }

  @Override
  public void initialize()
  {
  }

  @Override
  public void loadParameters(BufferedReader bufReader)
  {
  }

  @Override
  public void saveParameters(BufferedWriter bufWriter)
  {
  }
  
  @Override
  public String generateImportLab()
  {
    return null;
  }

  @Override
  public ModelTestCase runAlgorithm() throws InstantiationException, IllegalAccessException, SecurityException, IllegalArgumentException, ClassNotFoundException, NoSuchMethodException, InvocationTargetException
  {
    return null;
  }
}
