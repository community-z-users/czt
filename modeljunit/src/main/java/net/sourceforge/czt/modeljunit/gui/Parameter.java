/**
 * @author rong The TestingParameter class includes all the value of
 *         PanelTestDesign, Application can store these parameters into file or
 *         load them from file
 */

package net.sourceforge.czt.modeljunit.gui;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

public class Parameter
{
  public static final String DEFAULT_DIRECTORY = System.getProperty("user.dir");
  /**
   * Class name
   * */
  private static String m_strClassName;

  public static String getClassName()
  {
    return m_strClassName;
  }

  public static void setClassName(String classname)
  {
    m_strClassName = classname;
  }

  /**
   * The absolute path of model (class or java file)
   * */
  private static String m_strModelLocation;

  public static String getModelLocation()
  {
    return m_strModelLocation;
  }

  public static void setModelLocation(String location)
  {
    m_strModelLocation = location;
  }

  /**
   * Algorithm name
   * */
  private static String m_strAlgorithmName;

  public static String getAlgorithmName()
  {
    return m_strAlgorithmName;
  }

  public static void setAlgorithmName(String algorithmname)
  {
    m_strAlgorithmName = algorithmname;
  }

  /**
   * Test case name
   * */
  private static String m_strTestCaseVariableName;

  public static String getTestCaseVariableName()
  {
    return m_strTestCaseVariableName;
  }

  public static void setTestCaseVariableName(String name)
  {
    m_strTestCaseVariableName = name;
  }

  /**
   * Transition Coverage options 
   * */
  private static boolean[] m_bCoverageOption = new boolean[3];

  public static boolean[] getCoverageOption()
  {
    return m_bCoverageOption;
  }

  public static void setCoverageOption(boolean[] options)
  {
    m_bCoverageOption = options;
  }

  /**
   * Working directory
   * */
  private static String m_strModelChooserDirectory;

  public static String getModelChooserDirectory()
  {
    return m_strModelChooserDirectory;
  }
  
  public static void setModelChooserDirectory(String directory)
  {
    m_strModelChooserDirectory = directory;
  }

  /*
   * 0. Ues last time directory, 1. use default path
   * */
  private static int m_nFileChooserOpenMode;
  public static int getFileChooserOpenMode()
  {
    return m_nFileChooserOpenMode;
  }
  
  public static void setFileChooserOpenMode(int mode)
  {
    m_nFileChooserOpenMode = mode;
  }
  
  //
  private static File recreateSettingFile()
  {
    // Get the java file in the current directory 
    String currentDirectory = System.getProperty("user.dir");
    File file = new File(currentDirectory + File.separator + "setting.txt");
    if (file.exists())
      file.delete();
    // Create new setting file
    try {
      file.createNewFile();
    }
    catch (IOException e) {
      e.printStackTrace();
    }
    return file;
  }
  
  public static void createDefaultSettingFile()
  {
    String currentDirectory = System.getProperty("user.dir");
    File file = recreateSettingFile();
    // Write settings
    try {
      System.out.println("create default setting file");
      BufferedWriter out = new BufferedWriter(new FileWriter(file));
      out.write("Model directory=" + currentDirectory);
      out.close();
    }
    catch (IOException e) {
      e.printStackTrace();
    }

  }

  public static void readSettingFile()
  {
    // Get the java file in the current directory 
    String currentDirectory = System.getProperty("user.dir");
    File file = new File(currentDirectory + File.separator + "setting.txt");
    // Generate new setting file
    if (!file.exists()) {
      System.out.println(file.getAbsolutePath());
      Parameter.createDefaultSettingFile();
    }
    else
      System.out.println(file.getPath());
    try {
      BufferedReader in = new BufferedReader(new FileReader(file));
      String str;
      String[] parameters;
      while ((str = in.readLine()) != null) {
        parameters = str.split("=");
        if (parameters[0].equalsIgnoreCase("Model directory")) {
          m_strModelChooserDirectory = parameters[1];
        }
      }
      in.close();
    }
    catch (IOException e) {
    }

  }

  public static void wirteSettingFile()
  {
    File file = recreateSettingFile();
    // Write current settings
    try {
      System.out.println("create default setting file");
      BufferedWriter out = new BufferedWriter(new FileWriter(file));
      out.write("Model directory=" + Parameter.getModelChooserDirectory());
      out.close();
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }

  public String toString()
  {
    return "class name: " + m_strClassName + ", \nLocation: "
        + m_strModelLocation + ", \nAlgorithm: " + m_strAlgorithmName
        + ", \nCoverage: " + m_bCoverageOption[0] + ", " + m_bCoverageOption[1]
        + ", " + m_bCoverageOption[2] + ".";
  }
}
