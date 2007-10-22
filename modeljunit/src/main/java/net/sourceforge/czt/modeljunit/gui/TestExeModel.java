package net.sourceforge.czt.modeljunit.gui;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.io.StringWriter;
import java.io.Writer;
import java.lang.reflect.Method;
import java.util.ArrayList;

import javax.swing.DefaultListModel;
import javax.swing.event.EventListenerList;

import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
/**
 * To execute the test
 * */
public class TestExeModel
{
  public static final String[] COVERAGE_MATRIX = {"State coverage","Transition coverage","Transition pair coverage"};
  
  private static int m_nWalkLength;
  
  public static void setWalkLength(int length)
  {
    m_nWalkLength = length;
  }
  
  public static int getWalkLength()
  {
    return m_nWalkLength;
  }
  //-----------------------Run the test------------------------
  // private static Class<FsmModel> m_modelClass;
  private static Class<?> m_modelClass;
  private static FsmModel m_modelObject;
  public static Class<?> getModelClass()
  { return m_modelClass; }
  public static FsmModel getModelObject()
  { return m_modelObject;}
  
  public static boolean isModelLoaded()
  {
    if(m_modelClass == null || m_modelObject == null)
      return false;
    return true;
  }
  
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
    ClassFileLoader classLoader = ClassFileLoader.getInstance();

    String name[] = Parameter.getClassName().split("\\.");
    m_modelClass = classLoader.loadClass(name[0]);
    try {
      m_modelObject = (net.sourceforge.czt.modeljunit.FsmModel)m_modelClass.newInstance();
    }
    catch (InstantiationException e) {
      e.printStackTrace();
    }
    catch (IllegalAccessException e) {
      e.printStackTrace();
    }
  }
  
  /** 
   * The array of tester object
   * Using array because we need to separate several tester for different panel.
   * 0. For automatically run testing.
   * 1. For manually run testing.
   **/
  private static Tester[] m_tester = new Tester[2];
  public static void setTester(Tester tester, int idx)
  {
    m_tester[idx] = tester;
  }
  public static Tester getTester(int idx)
  {
    return m_tester[idx];
  }
  
  private static IAlgorithmParameter m_algo;
  public static void setAlgorithm(IAlgorithmParameter algo)
  {
    m_algo = algo;
  }
  
  private static ArrayList<Method> m_arrayMethod = new ArrayList<Method>();
  // Add an action method into list
  public static void addMethod(Method m)
  {
    m_arrayMethod.add(m);
  }
  public static ArrayList<Method> getMethodList()
  { 
    return m_arrayMethod;
  }
  // Run test automatically. This will be call when user press run button
  public static String runTestAuto()
  {
    
    String output = new String();
    // Redirect the system.out to result viewer text area component
    PrintStream ps = System.out; //Backup the System.out for later restore
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    System.setOut(new PrintStream(baos, true));
    // Run algorithm
    m_algo.runAlgorithm(0);
    // Set up coverage matrix to check the test result
    boolean[] bCoverage = Parameter.getCoverageOption();
    // Generate graph
    if(bCoverage[0]||bCoverage[1]||bCoverage[2])
      m_tester[0].buildGraph();
    CoverageHistory[] coverage = new CoverageHistory[3];
    if(bCoverage[0])
    {
      coverage[0] = new CoverageHistory(new StateCoverage(), 1);
      m_tester[0].addCoverageMetric(coverage[0]);
    }
    
    if(bCoverage[1])
    {
      coverage[1] = new CoverageHistory(new TransitionCoverage(), 1);
      m_tester[0].addCoverageMetric(coverage[1]);
    }
    
    if(bCoverage[2])
    {
      coverage[2] = new CoverageHistory(new TransitionPairCoverage(), 1);
      m_tester[0].addCoverageMetric(coverage[2]);
    }
    
    StringBuffer verbose = new StringBuffer();
    StringWriter sw = new StringWriter();
    if(Parameter.getVerbosity())
    {
      VerboseListener vl = new VerboseListener();
      m_tester[0].addListener(vl);
    }
    // Redirect model's output to string
    Model md = m_tester[0].getModel();
    Writer defWriter = md.getOutput();
    md.setOutput(sw);

    for(int i=0;i<3;i++)
      if(bCoverage[i])
        coverage[i].clear();
    // Generate test walking
    m_tester[0].generate(m_nWalkLength);
    // Print out generated graph
    if(bCoverage[0])
    {
      System.out.println(TestExeModel.COVERAGE_MATRIX[0]+" = "+coverage[0].toString());
      System.out.println(TestExeModel.COVERAGE_MATRIX[0]+" history = "+coverage[0].toCSV());
    }
    if(bCoverage[1])
    {
      System.out.println(TestExeModel.COVERAGE_MATRIX[1]+" = "+coverage[1].toString());
      System.out.println(TestExeModel.COVERAGE_MATRIX[1]+" history = "+coverage[1].toCSV());
    }
    if(bCoverage[2])
    {
      System.out.println(TestExeModel.COVERAGE_MATRIX[2]+" = "+coverage[2].toString());
      System.out.println(TestExeModel.COVERAGE_MATRIX[2]+" history = "+coverage[2].toCSV());
    }
    verbose = sw.getBuffer();
    // Reset model's output to default value
    md.setOutput(defWriter);
    // Recover System.out
    output = baos.toString();
    System.out.println(output);
    // Restore system.out to default value.
    System.setOut(ps);
    verbose.append(output);
    return verbose.toString();
  }
    
  public static void runTestManual()
  {}
}
