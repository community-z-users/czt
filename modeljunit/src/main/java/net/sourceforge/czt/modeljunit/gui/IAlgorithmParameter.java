
package net.sourceforge.czt.modeljunit.gui;


/*
 * IAlgorithmParameter.java
 * @author rong ID : 1005450 5th Aug 2007
 */

public interface IAlgorithmParameter
{
  /**
   * Initialize particular tester object.
   * Different panel might hold different test object.
   * This function provides a way to initialize different tester object.
   */
  public void initialize(int idx);

  /**
   * Generate any Java import statements that are needed in addition
   * to the standard modeljunit.* imports.
   * @return generated import statement
   */
  public String generateImportLab();

  /**
   *  Generates the Java code that sets up this algorithm to generate tests.
   *  The generated code will declare a variable 'Tester tester'.
   *  The returned code has already been indented correctly.
   */
  public String generateCode();

  public void runAlgorithm(int idx);
}
