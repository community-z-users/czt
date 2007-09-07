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
    SimCard model = new SimCardAdaptor();
    GreedyTester tester = new GreedyTester(model);
    tester.setResetProbability(0.001);
    //tester.buildGraph(1000000);
    //tester.addListener("Verbose", new VerboseListener(tester.getModel()));
    CoverageMetric trans = new TransitionCoverage();
    tester.addCoverageMetric(trans);
    tester.generate(100000);
    System.out.println("Transition coverage = "+trans.toString());
  }
}
