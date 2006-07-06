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

package net.sourceforge.czt.jdsl.graph.api;

import java.util.NoSuchElementException;

/**
 * Iterator over a set of vertices.  No order of the vertices is required  
 * by this interface, although order may be promised or required
 * by users of the interface.  Conceptually, the iterator starts out
 * positioned before the first vertex to be considered.  With each call
 * to next(), the iterator skips over another vertex and returns the vertex
 * skipped over, until the iterator is positioned past the last vertex.
 * 
 * Note that <code>NoSuchElementException</code> indicates two
 * different failure  states:  when the iterator is positioned before
 * the first vertex, vertex() and element() fail; when the iterator is
 * positioned after the last vertex, next() fails.
 *   
 * @version JDSL 2.1.1 
 * @author Mark Handy
 */
public interface VertexIterator extends net.sourceforge.czt.jdsl.core.api.PositionIterator {

    /**
     * @return Next vertex to consider
     * @exception NoSuchElementException if iterator has moved past
     * the last vertex to be seen
     */
    public Vertex nextVertex() throws NoSuchElementException;
    
    /** 
     * @return The vertex returned by the most recent next()
     * @exception NoSuchElementException When the iterator is in its
     * initial, before-the-first-vertex state
     */
    public Vertex vertex() throws NoSuchElementException;
    
}
