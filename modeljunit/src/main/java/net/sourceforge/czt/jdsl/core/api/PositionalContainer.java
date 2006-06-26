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

package net.sourceforge.czt.jdsl.core.api;



/** 
 * Positional containers (for example, sequences, trees, and graphs)
 * are containers in which elements are related to each other through
 * adjacency information.
 * <p>
 * A positional container stores elements at its positions and defines
 * adjacency relationships between the positions (for example,
 * before/after in a sequence, parent/child in a tree).  Thus, the model of
 * storage is topological -- i.e., a positional
 * container is a graph, or some restricted version of a graph. This means 
 * that the position at which an
 * element is stored is decided by the user and is arbitrary from
 * the point of view of the container.
 * <p>
 *
 * @see Position
 * @see Container
 * @version JDSL 2.1.1 
 * @author Mark Handy
 * @author Michael T. Goodrich
 * @author Roberto Tamassia
 * @author Mike Boilen (mgb)
 * @author Andrew Schwerin (schwerin)
 */
public interface PositionalContainer
extends InspectablePositionalContainer, Container {
    
    /** 
     * Swaps the elements associated with
     * the two positions, leaving
     * the positions themselves "where" they were.  
     * @param a First Position to swap
     * @param b Second Position to swap
     *
     * @exception InvalidAccessorException if either of <code>a</code>
     * and <code>b</code> is null or does not belong to this positional
     * container
     */
    public void swapElements (Position a, Position b) throws
	InvalidAccessorException;
    
}





