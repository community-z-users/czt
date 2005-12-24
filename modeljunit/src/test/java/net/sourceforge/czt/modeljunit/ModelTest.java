package net.sourceforge.czt.modeljunit;

import junit.framework.Test;
import junit.framework.TestSuite;

/**
 * Unit test for ModelJUnit
 */
public class ModelTest 
    extends ModelTestCase
{
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public ModelTest( String testName )
    {
        super( testName );
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite()
    {
        return new TestSuite( ModelTest.class );
    }

    public static void testRandomWalk()
    {
      FSM iut = new FSM();
      fsmLoad(iut.getClass());
      CoverageMetric actions = new ActionCoverage(fsmGetNumActions());
      addCoverage(actions);
      // fsmRandomWalk(new FSM(), 6, new Random());
      fsmRandomWalk(new FSM(), 10);
      System.out.println("Action coverage: "+actions);
      System.out.print("History: ");
      for (Float f : actions.getHistory())
        System.out.print(f*100.0F+", ");
      System.out.println();
    }
}
