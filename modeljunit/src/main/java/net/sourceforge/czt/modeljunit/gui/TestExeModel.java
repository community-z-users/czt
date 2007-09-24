package net.sourceforge.czt.modeljunit.gui;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.io.StringWriter;
import java.lang.reflect.Method;
import java.util.ArrayList;

import javax.swing.DefaultListModel;

import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;

public class TestExeModel
{
  private static int m_nWalkLength;
  
  public static void SetWalkLength(int length)
  {
    m_nWalkLength = length;
  }
  
  private static Tester m_tester;
  public static void SetTester(Tester tester)
  {
    m_tester = tester;
  }
  public static Tester getTester()
  {
    return m_tester;
  }
  
  private static IAlgorithmParameter m_algo;
  public static void SetAlgorithm(IAlgorithmParameter algo)
  {
    m_algo = algo;
  }
  
  private static ArrayList<Method> m_arrayMethod = new ArrayList<Method>();
  public static void ResetMethodList()
  {
    m_arrayMethod.clear();
    m_modelActoin.removeAllElements();
  }
  
  // The model for JList in PanelExecuteActions
  private static DefaultListModel m_modelActoin = new DefaultListModel();;
  public static DefaultListModel GetModelAction()
  {
    return m_modelActoin;
  }
  
  // Add an action method into list
  public static void AddMethod(Method m)
  {
    m_arrayMethod.add(m);
    m_modelActoin.addElement(m.getName());
  }
  public static ArrayList<Method> GetMethodList()
  { 
    return m_arrayMethod;
  }
  // Run test automatically. This will be call when user press run button
  public static String RunTestAuto()
  {
    String output = new String();
    // Redirect the system.out to result viewer text area component
    PrintStream ps = System.out; //Backup the System.out for later restore
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    System.setOut(new PrintStream(baos, true));
    // Run algorithm
    m_algo.runAlgorithm();
    // Set up coverage matrix to check the test result
    boolean[] bCoverage = Parameter.getCoverageOption();
    CoverageHistory[] coverage = new CoverageHistory[3];

    coverage[0] = new CoverageHistory(new StateCoverage(), 1);
    m_tester.addCoverageMetric(coverage[0]);
    
    coverage[1] = new CoverageHistory(new TransitionCoverage(), 1);
    m_tester.addCoverageMetric(coverage[1]);
    
    coverage[2] = new CoverageHistory(new TransitionPairCoverage(), 1);
    m_tester.addCoverageMetric(coverage[2]);
    
    StringBuffer verbose = new StringBuffer();
    StringWriter sw = new StringWriter();
    VerboseListener vl = new VerboseListener();
    m_tester.addListener(vl);
    Model md = m_tester.getModel();
    md.setOutput(sw);
    
    // Generate graph
    if(Parameter.getGenerateGraph())
      m_tester.buildGraph();
    // Clear coverage matrices
    for(int i=0;i<3;i++)
      if(bCoverage[i])
        coverage[i].clear();

    // Generate test walking
    m_tester.generate(m_nWalkLength);
    // Print out generated graph
    System.out.println("State history = "+coverage[0].toCSV());
    System.out.println("Transaction history = "+coverage[1].toCSV());
    System.out.println("Transaction pair history = "+coverage[2].toCSV());
    verbose = sw.getBuffer();
    // Recover System.out
    output = baos.toString();
    System.out.println(output);
    // Restore system.out to default value.
    System.setOut(ps);
    verbose.append(output);
    return verbose.toString();
  }
    
  public static void RunTestManual()
  {}
}
