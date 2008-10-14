/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.util.BitSet;
import java.util.List;

import junit.framework.Assert;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.examples.FSM;
import net.sourceforge.czt.modeljunit.examples.SimpleSetWithAdaptor;
import net.sourceforge.czt.modeljunit.examples.StringSetBuggy;

/**
 * Unit tests for Model
 */
public class ModelTest extends TestCase
{
  private String message_ = null;

  /**
   * Create the test case
   *
   * @param testName name of the test case
   */
  public ModelTest(String testName)
  {
    super(testName);
  }

  /**
   * @return the suite of tests being tested
   */
  public static Test suite()
  {
    return new TestSuite(ModelTest.class);
  }

  public static void testReflection()
  {
    FSM sut = new FSM();
    Model model = new Model(sut);
    assertEquals(sut, model.getModel());
    assertEquals(FSM.class, model.getModelClass());
    assertEquals("net.sourceforge.czt.modeljunit.examples.FSM",
        model.getModelName());
    assertEquals(4, model.getNumActions());
    Assert.assertEquals("0", model.getCurrentState());
    int action0 = model.getActionNumber("action0");
    int action1 = model.getActionNumber("action1");
    int action2 = model.getActionNumber("action2");
    int actionNone = model.getActionNumber("actionNone");
    int rubbish = model.getActionNumber("rubbish");
    Assert.assertTrue(action0 >= 0);
    Assert.assertTrue(action1 >= 0);
    Assert.assertTrue(action2 >= 0);
    Assert.assertTrue(actionNone >= 0);
    Assert.assertEquals(-1, rubbish);
    Assert.assertEquals("action0", model.getActionName(action0));
    Assert.assertEquals("action1", model.getActionName(action1));
    Assert.assertEquals("action2", model.getActionName(action2));
    Assert.assertEquals("actionNone", model.getActionName(actionNone));
  }


  public static void testFlag()
  {
    FSM sut = new FSM();
    Model model = new Model(sut);
    assertTrue(model.getTesting());
    assertTrue(model.setTesting(false));
    assertFalse(model.getTesting());
    assertFalse(model.setTesting(true));
    assertTrue(model.getTesting());
  }

  public static void testOutput()
  {
    FSM sut = new FSM();
    Model model = new Model(sut);
    Writer wr0 = model.getOutput();
    assertTrue(wr0 instanceof OutputStreamWriter);
    Writer wr1 = new StringWriter();
    assertEquals(wr0, model.setOutput(wr1));
    assertEquals(wr1, model.getOutput());
    model.printMessage("test");
    model.printWarning("warning");
    Writer wr2 = new OutputStreamWriter(System.out);
    assertEquals(wr1, model.setOutput(wr2));
    assertEquals(wr2, model.getOutput());
    model.printMessage("ignore this message"); // should NOT go into wr1.
    assertEquals("test\nWarning: warning\n", wr1.toString());
  }

  public static void testEnabled()
  {
    Model model = new Model(new FSM());
    int action0 = model.getActionNumber("action0");
    int action1 = model.getActionNumber("action1");
    int action2 = model.getActionNumber("action2");
    int actionNone = model.getActionNumber("actionNone");
    Object s0 = model.getCurrentState();
    assertEquals("0", s0);

    // check enabled actions of state 0.
    BitSet enabled0 = model.enabledGuards();
    assertEquals(2, enabled0.cardinality());
    assertEquals(false, enabled0.get(action0));
    assertEquals(false, enabled0.get(action1));
    assertEquals(true, enabled0.get(action2));
    assertEquals(true, enabled0.get(actionNone));

    // Now take action2, to state 2, and check its enabled actions.
    model.doAction(action2);
    assertEquals("2", model.getCurrentState().toString());
    BitSet enabled2 = model.enabledGuards();
    assertEquals(true, enabled2.get(action0));
    assertEquals(true, enabled2.get(action1));
    assertEquals(false, enabled2.get(action2));
    assertEquals(true, enabled2.get(actionNone));

    // Now check that reset returns to the initial state.
    model.doReset();
    assertEquals(s0, model.getCurrentState());
    assertEquals(enabled0, model.enabledGuards());
  }

  public void testFailureContinues()
  {
    SimpleSetWithAdaptor sut = new SimpleSetWithAdaptor(new StringSetBuggy());
    Model model = new Model(sut);
    int addS1 = model.getActionNumber("addS1");
    try {
      assertTrue(model.doAction(addS1));
    }
    catch (TestFailureException ex) {
      fail("Test failures should not throw exceptions, by default");
    }
  }

  public void testFailure()
  {
    SimpleSetWithAdaptor sut = new SimpleSetWithAdaptor(new StringSetBuggy());
    Model model = new Model(sut);
    model.addListener(new StopOnFailureListener());
    int addS1 = model.getActionNumber("addS1");
    try {
      assertTrue(model.doAction(addS1));
      fail("Action delS2 (with sut=StringSetBuggy) should have failed");
    }
    catch (TestFailureException ex) {
      assertEquals("failure in action addS1 from state FF due to ",
          ex.getMessage().subSequence(0, 45));
      assertEquals("FF", ex.getState());
      assertEquals("addS1", ex.getActionName());
      assertEquals(sut, ex.getModel());
      assertEquals(sut.getClass().getName(), ex.getModelName());
      List<Transition> trs = ex.getSequence();
      assertEquals(0, trs.size());
    }
  }

  public void testListener()
  {
    Model model = new Model(new FSM());
    ModelListener dummy = new AbstractListener()
      {
        public String getName() {return "dummy";}
        @Override public void doneReset(String reason, boolean testing)
        {
          message_ += "doneReset("+reason+","+testing+")";
        }

        public void doneGuard(Object state, int action, boolean enabled, int value)
        {
          message_ += "doneGuard("+state+","+action+","+enabled+","+value+")";
        }

        public void startAction(Object state, int action, String name)
        {
          message_ += "startAction("+state+","+action+","+name+")";
        }

        public void doneTransition(int action, Transition tr)
        {
          message_ += "doneTransition("+action+","+tr.toString()+")";
        }
      };
    assertNull(model.getListener("dummy"));
    assertEquals(dummy, model.addListener(dummy));
    assertEquals(dummy, model.getListener("dummy"));
    assertEquals(1, model.getListenerNames().size());
    // TODO: test model.addListener("verbose");
    int action1 = model.getActionNumber("action1");
    int action2 = model.getActionNumber("action2");
    message_ = "";
    // now start creating model events.
    assertTrue(model.isEnabled(action2));
    assertEquals("doneGuard(0,"+action2+",true,1)", message_);
    message_ = "";
    assertFalse(model.isEnabled(action1));
    assertEquals("doneGuard(0,"+action1+",false,0)", message_);
    message_ = "";
    assertTrue(model.doAction(action2));
    assertEquals("doneGuard(0,"+action2+",true,1)"
        + "startAction(0,"+action2+",action2)"
        + "doneTransition("+action2+",(0, action2, 2))", message_);
    message_ = "";
    model.doReset();
    assertEquals("doneReset(User,true)", message_);

    // now remove the listener and check that it is no longer called
    assertEquals(dummy, model.removeListener("dummy"));
    assertNull(model.getListener("dummy"));
    message_ = "";
    model.doReset();
    assertEquals("", message_);

    // test getListenerNames then removeAll.
    model.addListener("graph");
    assertTrue(model.getListener("graph") instanceof GraphListener);
    assertEquals(model.getGraphListener(), model.getListener("graph"));
    assertEquals(1, model.getListenerNames().size());
    assertEquals(model.getGraphListener(), new RandomTester(model).buildGraph());
    model.addListener(new TransitionCoverage());
    TransitionCoverage tr = (TransitionCoverage) model.getListener("transition coverage");
    assertEquals(2, model.getListenerNames().size());
    assertEquals(5, tr.getMaximum()); // it should have been given the graph
    assertEquals("0/5", tr.toString());
    model.removeAllListeners();
    assertEquals(0, model.getListenerNames().size());
  }
}
