package net.sourceforge.czt.modeljunit;

import java.util.BitSet;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.examples.FSM;
import junit.framework.TestCase;

public class GraphListenerTest extends TestCase
{
  public static void testBuildGraph()
  {
    Model model = new Model(new FSM());
    GraphListener listen = (GraphListener) model.addListener("graph");
    assertNotNull(listen);
    assertEquals(new BitSet(), listen.getDone(model.getCurrentState()));
    Object state0 = model.getCurrentState();
    BitSet todo = listen.getTodo(state0);
    BitSet done = listen.getDone(state0);
    assertEquals(2, todo.cardinality());
    assertEquals(0, done.cardinality());
    model.doAction(model.getActionNumber("action2"));
    // the todo and done sets should have been updated
    assertEquals(1, todo.cardinality());
    assertEquals(1, done.cardinality());
    Object state2 = model.getCurrentState();
    todo = listen.getTodo(state2);
    done = listen.getDone(state2);
    assertEquals(3, todo.cardinality());
    assertEquals(0, done.cardinality());
    assertEquals(listen, new RandomTester(model).buildGraph());
    InspectableGraph graph = listen.getGraph();
    // now check that the correct graph has been built.
    assertEquals(3, graph.numVertices());
    assertEquals(5, graph.numEdges());
    Vertex s0 = listen.getVertex("0");
    Vertex s1 = listen.getVertex("1");
    Vertex s2 = listen.getVertex("2");
    assertNotNull(s0);
    assertNotNull(s1);
    assertNotNull(s2);
    assertEquals("0", s0.element());
    assertEquals("1", s1.element());
    assertEquals("2", s2.element());
    // we must iterate through the edges, because graph.aConnectingEdge
    // does not respect the direction of the edge!
    EdgeIterator iter = graph.edges();
    while (iter.hasNext()) {
      Edge e = iter.nextEdge();
      if (graph.origin(e) == s2 && graph.destination(e) == s0)
        assertEquals("action0", e.element());
      else if (graph.origin(e) == s2 && graph.destination(e) == s1)
        assertEquals("action1", e.element());
      else if (graph.origin(e) == s0 && graph.destination(e) == s2)
        assertEquals("action2", e.element());
      else
        assertEquals("actionNone", e.element());
    }
  }
}