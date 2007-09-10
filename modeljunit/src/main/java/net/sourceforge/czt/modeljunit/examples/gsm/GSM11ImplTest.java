package net.sourceforge.czt.modeljunit.examples.gsm;

import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import junit.framework.TestCase;

public class GSM11ImplTest extends TestCase
{

  protected void setUp() throws Exception
  {
    super.setUp();
  }

  public void testGSM11()
  {
    SimCard model = new SimCard(new SimCardAdaptor());
    RandomTester tester = new RandomTester(model);
    tester.setResetProbability(0.01);
    //tester.buildGraph(1000000);
    //tester.addListener("Verbose", new VerboseListener(tester.getModel()));
    CoverageMetric trans = new TransitionCoverage();
    tester.addListener(trans);
    tester.generate(10000);
    System.out.println("Transition coverage = "+trans.toString());
  }

  /** In case we want to run this JUnit test from the command line. */
  public static void main(String[] args) throws Exception
  {
    GSM11ImplTest test = new GSM11ImplTest();
    test.setUp();
    test.testGSM11();
  }
}
