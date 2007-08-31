
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
   * Code generator
   * */
  public String generateImportLab();
  public String generateCode();

  /**
   * Run code to see the result
   * @throws InvocationTargetException
   * @throws NoSuchMethodException
   * @throws ClassNotFoundException
   * @throws IllegalArgumentException
   * @throws SecurityException
   * */
  public Tester runAlgorithm()
    throws InstantiationException,
      IllegalAccessException,
      SecurityException,
      IllegalArgumentException,
      ClassNotFoundException,
      NoSuchMethodException,
      InvocationTargetException;
}
