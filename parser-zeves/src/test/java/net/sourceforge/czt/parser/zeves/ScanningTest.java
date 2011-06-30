package net.sourceforge.czt.parser.zeves;

import java.util.Arrays;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for simple App.
 */
public class ScanningTest
    extends TestCase
{

    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public ScanningTest( String testName )
    {
        super( testName );
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite()
    {
        return new TestSuite( ScanningTest.class );
    }

    /**
     * Rigourous Test :-)
     */
    public void testScanning()
    {
       // LatexScannerDebugger.main(new String[] { "/Users/nljsf/Documents/research/java/netbeans/czt/parser-zeves/src/test/resources/tests/zeves/simple.tex" });
        System.out.println("HELLO!");
        assertTrue( true );
    }
}
