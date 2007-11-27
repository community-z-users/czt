
package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.lang.reflect.InvocationTargetException;

import net.sourceforge.czt.modeljunit.Tester;

/**
 * IAlgorithmParameter.java
 *
 * @author rong
 * ID : 1005450
 * 5th Aug 2007
 * */

public interface IAlgorithmParameter
{
  /**
   * Initialize particular tester object.
   * Different panel might hold different test object.
   * This function provides a way to initialize different tester object.
   * */
  public void initialize(int idx);

  /**
   * Generate import statement to include libraries
   * @return generated import statement
   */
  public String generateImportLab();
  /**
   * Code generator, to generate test code by using this function
   * */
  public String generateCode();

  public void runAlgorithm(int idx);
}
