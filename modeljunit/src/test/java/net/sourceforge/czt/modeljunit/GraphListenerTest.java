package net.sourceforge.czt.modeljunit;

import java.util.BitSet;

import org.junit.Test;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.examples.FSM;
import junit.framework.TestCase;

public class GraphListenerTest extends TestCase
{
  @Test
  public static void testBuildGraph()
  {
    Model model = new Model(new FSM());
    GraphListener listen = (GraphListener) model.addListener("graph");
    checkGraph(model, listen, false);
  }

  @Test
  public void testClear()
  {
    Model model = new Model(new FSM());
    GraphListener listen = (GraphListener) model.addListener("graph");
    checkGraph(model, listen, false);
    listen.clearDoneTodo();
    assertEquals(true, listen.isComplete()); // should remember it was complete
    // now run the same tests again, starting from empty todo/done sets,
    // but with the graph already constructed.
    checkGraph(model, listen, true);
  }

  /** A helper method that checks the gradual construction of
   *  the todo and done bitsets, then the structure of the graph.
   * @param model
   * @param listen
   * @param repeat true if the graph is already complete
   */
  protected static void checkGraph(Model model, GraphListener listen, 
      boolean complete)
  {
    assertNotNull(listen);
    assertEquals(new BitSet(), listen.getDone(model.getCurrentState()));
    Object state0 = model.getCurrentState();
    BitSet todo = listen.getTodo(state0);
    BitSet done = listen.getDone(state0);
    assertEquals(2, todo.cardinality());
    assertEquals(0, done.cardinality());
    assertEquals(complete, listen.isComplete());
    assertEquals(2, listen.numTodo());
    
    // take action2 (from state 0 to state 2).
    int action2 = model.getActionNumber("action2");
    model.doAction(action2);
    // our local todo and done sets should be unchanged
    assertEquals(2, todo.cardinality());
    assertEquals(0, done.cardinality());
    // but they should have been updated within the graph
    todo = listen.getTodo(state0);
    done = listen.getDone(state0);
    assertEquals(1, todo.cardinality());
    assertEquals(1, done.cardinality());

    Object state2 = model.getCurrentState();
    todo = listen.getTodo(state2);
    done = listen.getDone(state2);
    assertEquals(3, todo.cardinality());
    assertEquals(0, done.cardinality());
    assertEquals(complete, listen.isComplete());
    assertEquals(4, listen.numTodo());

    // take action0 (from state 2 back to state 0)
    int action0 = model.getActionNumber("action0");
    model.doAction(action0);
    // our local todo and done sets should be unchanged
    assertEquals(3, todo.cardinality());
    assertEquals(0, done.cardinality());
    // but they should have been updated within the graph
    todo = listen.getTodo(state2);
    done = listen.getDone(state2);
    assertEquals(2, todo.cardinality());
    assertEquals(1, done.cardinality());
    assertEquals(true, done.get(action0));
    assertEquals(false, todo.get(action0));
    assertEquals(false, todo.get(action2));
    for (int i=0; i<model.getNumActions(); i++) {
      assertEquals("action "+model.getActionName(i),
          done.get(i), listen.isDone(state2, i));
    }
    for (int i=0; i<model.getNumActions(); i++) {
      assertEquals("action "+model.getActionName(i),
          todo.get(i), listen.isTodo(state2, i));
    }
    
    // now build the rest of the graph and check its structure
    assertEquals(listen, new RandomTester(model).buildGraph(1000,false));
    assertEquals(true, listen.isComplete());
    assertEquals(0, listen.numTodo());
    for (int i=0; i<model.getNumActions(); i++) {
      assertEquals("action "+model.getActionName(i),
          0, listen.getTodo(i).cardinality());
    }
    assertEquals(2, listen.getDone(state0).cardinality());
    assertEquals(3, listen.getDone(state2).cardinality());
    
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