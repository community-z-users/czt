package net.sourceforge.czt.modeljunit;

import junit.framework.Test;
import junit.framework.TestCase;
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

    public void testRandomWalk()
    {
      // fsmRandomWalk(new FSM(), 6, new Random());
      fsmRandomWalk(new FSM(), 10);
      // TODO: check coverage
    }

}
