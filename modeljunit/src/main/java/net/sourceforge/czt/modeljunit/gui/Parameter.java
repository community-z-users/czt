/**
 * @author rong 
 * The TestingParameter class includes all the value of
 * PanelTestDesign, Application can store these parameters into file or
 * load them from file
 */

package net.sourceforge.czt.modeljunit.gui;

public class Parameter
{
  /**
   * Class name
   * */
  private static String m_strClassName;
  public static String getClassName()
  {return m_strClassName;}
  public static void setClassName(String classname)
  {m_strClassName = classname;}
  /**
   * The absolute path of model (class or java file)
   * */
  public static String m_strModelLocation;
  public static String getModelLocation()
  { return m_strModelLocation; }
  public static void setModelLocation(String location)
  { m_strModelLocation = location;}
  /**
   * Algorithm name
   * */
  public static String m_strAlgorithmName;
  public static String getAlgorithmName()
  { return m_strAlgorithmName; }
  public static void setAlgorithmName(String algorithmname)
  { m_strAlgorithmName = algorithmname; }
  
  /**
   * Test case name
   * */
  public static String m_strTestCaseVariableName;
  public static String getTestCaseVariableName()
  { return m_strTestCaseVariableName; }
  public static void setTestCaseVariableName(String name)
  { m_strTestCaseVariableName = name; }
  
  /**
   * Transition Coverage options 
   * */
  public static boolean[] m_bCoverageOption = new boolean[3];
  public static boolean[] getCoverageOption()
  { return m_bCoverageOption; }
  public static void setCoverageOption(boolean[] options)
  { m_bCoverageOption = options; }
/*  
  public static void initParameter(String className, String path, String algorithmName,
      boolean[] coverage)
  {
    m_strClassName = className;
    m_strModelLocation = path;
    m_strAlgorithmName = algorithmName;
    m_bCoverageOption = coverage;
  }
*/
  public String toString()
  {
    return "class name: " + m_strClassName + ", \nLocation: "
        + m_strModelLocation + ", \nAlgorithm: " + m_strAlgorithmName
        + ", \nCoverage: " + m_bCoverageOption[0] + ", " + m_bCoverageOption[1]
        + ", " + m_bCoverageOption[2] + ".";
  }
}
