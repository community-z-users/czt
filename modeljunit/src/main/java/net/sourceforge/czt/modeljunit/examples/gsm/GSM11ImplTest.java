package net.sourceforge.czt.modeljunit.examples.gsm;

import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
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
    Tester tester = new RandomTester(model);
    tester.addListener("Verbose", new VerboseListener(tester.getModel()));
    tester.generate(20);
  }
}
