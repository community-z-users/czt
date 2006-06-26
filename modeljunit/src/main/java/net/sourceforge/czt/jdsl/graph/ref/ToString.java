/*
  Copyright (c) 1999, 2000 Brown University, Providence, RI
  
                            All Rights Reserved
  
  Permission to use, copy, modify, and distribute this software and its
  documentation for any purpose other than its incorporation into a
  commercial product is hereby granted without fee, provided that the
  above copyright notice appear in all copies and that both that
  copyright notice and this permission notice appear in supporting
  documentation, and that the name of Brown University not be used in
  advertising or publicity pertaining to distribution of the software
  without specific, written prior permission.
  
  BROWN UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
  SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR ANY PARTICULAR PURPOSE.  IN NO EVENT SHALL BROWN
  UNIVERSITY BE LIABLE FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL
  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
  PERFORMANCE OF THIS SOFTWARE.
*/

package net.sourceforge.czt.jdsl.graph.ref;

import net.sourceforge.czt.jdsl.graph.api.*;

/** 
 * string representing a graph.  Since
 * all the useful methods are static, it should never be necessary to
 * create an instance of ToString.  Until I get around to writing
 * better documentation here, see net.sourceforge.czt.jdsl.core.ref.ToString for the style
 * I use here.
 * 
 * @author Mark Handy
 * @version JDSL 2.1.1 
 */
public class ToString {

  private ToString() { }


  public static interface VertexToString {
    String stringfor( Vertex v );
  }

  public static interface EdgeToString {
    String stringfor( Edge e, InspectableGraph g );
  }



  public static final VertexToString vert_to_element_s =
    new VertexWritesElementOnly();
  
  public static final EdgeToString edge_in_rt_style =
    new EdgeInRTStyle( vert_to_element_s );

  /** 
   * Code lifted shamelessly from rt's corresponding class in
   * jdsltools.testers.graph, then adapted to the style of my
   * net.sourceforge.czt.jdsl.core.ref.ToString.
   */
  public static String stringfor( InspectableGraph g,
				  VertexToString vts,
				  EdgeToString ets ) {
    String s;
    s = "numVertices: " + g.numVertices();
    s = s + "        numEdges: " + g.numEdges() + "\n";
    s = s + "vertices:\n";
    VertexIterator vertices = g.vertices();
    while (vertices.hasNext()) {
      s = s + "  " + vts.stringfor( vertices.nextVertex() ) + "\n";
    }
    s = s + "edges:\n";
    EdgeIterator edges = g.edges();
    while (edges.hasNext()) {
      s = s + ets.stringfor( edges.nextEdge(), g ) + "\n";
    }
    return s;
  }
  
  public static String stringfor( InspectableGraph g ) {
    return stringfor( g, vert_to_element_s, edge_in_rt_style );
  }
  
  
  
  public static String stringfor( Edge e ) {
    return "edge with element " + e.element();
  }
  
  public static String stringfor (Vertex v ) {
    return "vertex with element " + v.element();
  }
  

  // nested class(es)

  public static class VertexWritesElementOnly implements VertexToString {
    public String stringfor( Vertex v ) { return "" + v.element(); }
  }

  public static class EdgeInRTStyle implements EdgeToString {
    private VertexToString vts_m;
    EdgeInRTStyle( VertexToString vts ) { vts_m = vts; }
    public String stringfor( Edge e, InspectableGraph g ) {
      String arrow;
      if( g.isDirected(e) ) arrow = " -> ";
      else arrow = " -- ";
      Vertex[] ends = g.endVertices(e);
      String orig = vts_m.stringfor( ends[0] );
      String dest = vts_m.stringfor( ends[1] );
      return "  [" + orig + arrow + dest + "]    " + e.element();
    }
  }
  
  public static class VertexToEmptyString implements VertexToString {
    public String stringfor( Vertex v ) { return ""; }
  }
  
  public static class EdgeToEmptyString implements EdgeToString {
    public String stringfor( Edge e, InspectableGraph g ) { return ""; }
  }
  
}
