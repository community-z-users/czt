package algo;

import jdsl.graph.api.*;
import jdsl.graph.algo.IntegerDijkstraPathfinder;
import support.*;

/**
 * An extension of the IntegerDijkstraPathfinder class to find
 * shortest time paths between airports.
 *
 * @version JDSL 2
 */
//b7.4
public class FlightDijkstra extends IntegerDijkstraPathfinder {
//e7.4

  //b7.5
  private int startTime_;
  //e7.5

  /** 
   * Calculates the weight of an edge.  In our case, the weight is the
   * total time (in minutes) between the time a passenger is scheduled
   * to arrive at the origin airport and the time the plane is
   * scheduled to arrive at the destination airport.  Note this is not
   * realistic, since it doesn't take into account minimum required
   * layover times.
   */
  //b7.6  
  protected int weight (Edge e) {
    // the flightspecs for the flight along Edge e
    FlightSpecs eFS = (FlightSpecs)e.element();
    int connectingTime = TimeTable.diff(eFS.departureTime(), startTime_ + distance(g_.origin(e)));
    return connectingTime + eFS.flightDuration();
  }
  //e7.6

  //b7.7
  public void execute(InspectableGraph g, Vertex source, Vertex dest, int startTime) throws InvalidVertexException {
    startTime_ = startTime;
    super.execute(g,source,dest);
  }
  //e7.7

  /* ************************************ */ 
  /* Members not described in the lesson. */
  /* ************************************ */ 
    
  protected EdgeIterator incidentEdges (Vertex v) {
    return g_.incidentEdges(v,EdgeDirection.OUT);
  }

} 
