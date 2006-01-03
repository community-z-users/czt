/**
Copyright (C) 2006 Mark Utting
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

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;

import junit.framework.Assert;
import junit.framework.Test;
import junit.framework.TestSuite;
import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeDirection;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;

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

    public static void testEnabled()
    {
      fsmInit(new FSM(), true);
      Assert.assertEquals("0", fsmGetState());
      int action0 = fsmGetAction("action0");
      int action1 = fsmGetAction("action1");
      int action2 = fsmGetAction("action2");
      int actionNone = fsmGetAction("actionNone");
      int rubbish = fsmGetAction("rubbish");
      Assert.assertTrue(action0 >= 0);
      Assert.assertTrue(action1 >= 0);
      Assert.assertTrue(action2 >= 0);
      Assert.assertTrue(actionNone >= 0);
      Assert.assertEquals(-1, rubbish);
      Assert.assertEquals("action0", fsmGetActionName(action0));
      Assert.assertEquals("action1", fsmGetActionName(action1));
      Assert.assertEquals("action2", fsmGetActionName(action2));
      Assert.assertEquals("actionNone", fsmGetActionName(actionNone));
      
      // check enabled actions of state 0.
      BitSet enabled = fsmEnabledActions();
      Assert.assertEquals(false, enabled.get(action0));
      Assert.assertEquals(false, enabled.get(action1));
      Assert.assertEquals(true,  enabled.get(action2));
      Assert.assertEquals(true,  enabled.get(actionNone));

      // Now take action2, to state 2, and check its enabled actions.
      fsmDoAction(action2);
      Assert.assertEquals("2", fsmGetState().toString());
      enabled = fsmEnabledActions();
      Assert.assertEquals(true,  enabled.get(action0));
      Assert.assertEquals(true,  enabled.get(action1));
      Assert.assertEquals(false, enabled.get(action2));
      Assert.assertEquals(true,  enabled.get(actionNone));
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
      Assert.assertEquals(0.0F, hist.get(0), 0.01F);
    }
    
    public static void testBuildGraph()
    {
      FSM iut = new FSM();
      fsmBuildGraph(iut, new Random(123456789));
      InspectableGraph graph = fsmGetGraph();
      // now check that the correct graph has been built.
      Assert.assertEquals(3, graph.numVertices());
      Assert.assertEquals(5, graph.numEdges());
      Vertex s0 = fsmGetVertex("0");
      Vertex s1 = fsmGetVertex("1");
      Vertex s2 = fsmGetVertex("2");
      Assert.assertNotNull(s0);
      Assert.assertNotNull(s1);
      Assert.assertNotNull(s2);
      Assert.assertEquals("0", s0.element());
      Assert.assertEquals("1", s1.element());
      Assert.assertEquals("2", s2.element());
      // we must iterate through the edges, because graph.aConnectingEdge
      // does not respect the direction of the edge!
      EdgeIterator iter = graph.edges();
      while (iter.hasNext()) {
        Edge e = iter.nextEdge();
        if (graph.origin(e) == s2 && graph.destination(e) == s0)
          Assert.assertEquals("action0", e.element());
        else if (graph.origin(e) == s2 && graph.destination(e) == s1)
          Assert.assertEquals("action1", e.element());
        else if (graph.origin(e) == s0 && graph.destination(e) == s2)
          Assert.assertEquals("action2", e.element());
        else
          Assert.assertEquals("actionNone", e.element());
      }
    }
}
