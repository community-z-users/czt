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

import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.ModelTestCase;

public class Parameter
{
  public static final String DEFAULT_DIRECTORY = System.getProperty("user.dir");
  private static boolean m_bGenerateGraph;
  public static boolean getGenerateGraph()
  { return m_bGenerateGraph; }
  public static void setGenerateGraph(boolean print)
  { m_bGenerateGraph = print; }
  /**
   * Reset probability
   * 
   * Set the probability of doing a reset during random walks. 
   * Note that the average length of each test sequence will 
   * be roughly proportional to the inverse of this probability. 
   * 
   * If this is set to 0.0, then resets will only be done 
   * when we reach a dead-end state (no enabled actions). 
   * This means that if the FSM contains a loop that does not 
   * have a path back to the initial state, then the random walks 
   * may get caught in that loop forever. For this reason, 
   * a non-zero probability is recommended. 
   * */
  // private static double m_nResetProbility = ModelTestCase.DEFAULT_RESET_PROBABILITY;
  private static double m_nResetProbility = 0.05;
  public static double getResetProbility()
  { return m_nResetProbility; }
  public static void setResetProbility(double probility)
  { m_nResetProbility = probility; }
  
  /**
   * Test generation verbosity
   * 
   * verbosity - 0..3
   * */
  private static int m_nVerbosity = 2;
  public static int getVerbosity()
  { return m_nVerbosity; }
  public static void setVerbosity(int verb)
  { m_nVerbosity = verb;}
  
  /**
   * Test failure verbosity
   * 
   * failureVerbosity - 0..3
   * */
  private static int m_nFailureVerbosity;
  public static int getFailureVerbosity()
  { return m_nFailureVerbosity; }
  public static void setFailureVerbosity(int verb)
  { m_nFailureVerbosity = verb; }
  
  /**
   * Class name, just includes the name of the class and suffix
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
   * The absolute path of model (class or java file) includes path ane file name
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
    if (!file.exists()) 
    {
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
  // -----------------------Run the test------------------------
  // private static Class<FsmModel> m_modelClass;
  private static Class<?> m_modelClass;
  private static FsmModel m_modelObject;
  public static Class<?> getModelClass(){ return m_modelClass; }
  public static FsmModel getModelObject(){ return m_modelObject;}
  
  /**
   * If user loaded an invalid model class, the model class and model object
   * have to be reset to null.
   * */
  public static void resetModelToNull()
  {
    m_modelClass = null;
    m_modelObject = null;
  }
  public static void loadModelClassFromFile()
  {
    ClassFileLoader classLoader = ClassFileLoader.createLoader();
    String name[] = Parameter.getClassName().split("\\.");
    m_modelClass = classLoader.findClass(name[0]);
    try {
      m_modelObject = (FsmModel)m_modelClass.newInstance();
    }
    catch (InstantiationException e) {
      e.printStackTrace();
    }
    catch (IllegalAccessException e) {
      e.printStackTrace();
    }
  }
  
  //----------------------Override toString----------------------
  public String toString()
  {
    return "class name: " + m_strClassName + ", \nLocation: "
        + m_strModelLocation + ", \nAlgorithm: " + m_strAlgorithmName
        + ", \nCoverage: " + m_bCoverageOption[0] + ", " + m_bCoverageOption[1]
        + ", " + m_bCoverageOption[2] + ".";
  }
}
