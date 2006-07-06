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
 * An abstraction of the notion of a "place" in a
 * container -- where an element is stored relative to other elements in
 * the container.  (A node of a tree and a vertex of a graph are examples of
 * positions.)  Conceptually, what Position adds to Accessor's ability to
 * get an element is the ability to get such topological information; but
 * the nature of the topological information varies with the container,
 * so there are no new methods here.
 *
 * <p>When a
 * position is no longer used by the container it is marked as
 * <i>invalid</i> and any subsequent use of that position provokes an
 * <code>InvalidAccessorException</code>.  An InvalidAccessorException
 * is also thrown when a Position belongs to a different container
 * (either a container of a different type, or another container of this
 * same type).
 * <p> Two possible implementations of a position: as a
 * wrapper around an index into an array, or as a reference to a node.
 *
 * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Benoit Hudson (bh)
 * @author Andrew Schwerin (schwerin)
 * @author Michael T. Goodrich
 * @author Roberto Tamassia
 * @see PositionalContainer */

public interface Position extends Accessor, Decorable {

}
