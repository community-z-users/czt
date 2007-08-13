
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;

public interface IAlgorithmParameter
{
  public void initialize();

  /**
   * Save parameters into configuration file
   * */
  public void saveParameters(BufferedWriter bufWriter);

  /**
   * Load parameters from configuration file
   * */
  public void loadParameters(BufferedReader bufReader);

  /**
   * Code generater
   * */
  public String generateImportLab();
  public String generateCode();
}
