package net.sourceforge.czt.modeljunit;

import java.util.ArrayList;

import junit.framework.Assert;
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
      fsmRandomWalk(new FSM(), 10);
      Assert.assertEquals(0.75F, actions.getPercentage(), 0.01F);
      ArrayList<Float> hist = actions.getHistory();
      Assert.assertNotNull(hist);
      Assert.assertEquals("Incorrect history size.", 11, hist.size());
      Assert.assertEquals(0.0F, hist.get(0), 0.01F);
      
      // we print this just for interest
      System.out.println("Action coverage: "+actions);
      System.out.print("History: ");
      for (Float f : actions.getHistory())
        System.out.print(f*100.0F+", ");
      System.out.println();
      
      fsmResetCoverage();
      hist = actions.getHistory();
      Assert.assertNotNull(hist);
      Assert.assertEquals("History not reset.", 1, hist.size());
    }
}
