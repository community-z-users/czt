
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;

import javax.swing.JPanel;

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
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void initialize()
  {
    // TODO Auto-generated method stub

  }

  @Override
  public void loadParameters(BufferedReader bufReader)
  {
    // TODO Auto-generated method stub

  }

  @Override
  public void saveParameters(BufferedWriter bufWriter)
  {
    // TODO Auto-generated method stub

  }
  @Override
  public String generateImportLab()
  {
    // TODO Auto-generated method stub
    return null;
  }

}
