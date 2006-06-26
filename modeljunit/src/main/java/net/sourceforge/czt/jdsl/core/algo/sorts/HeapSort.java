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

package net.sourceforge.czt.jdsl.core.algo.sorts;

import net.sourceforge.czt.jdsl.core.api.*;
import net.sourceforge.czt.jdsl.core.ref.ArrayHeap;



/**
 * Performs a heap-sort in O(n log n) time, provided only that
 * the replaceElement(.) method of the Sequence works in O(1) time
 * (and thus the style of implementation of the Sequence is not relevant).
 * All of the Positions of the sequence are preserved, but their
 * elements are moved around.
 *
 * @author Benoit Hudson (bh)
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public class HeapSort implements SortObject {
  
  public void sort (Sequence s, Comparator c) {
    PriorityQueue pq = new ArrayHeap(c,s.size()+1,false);

    PositionIterator pi = s.positions();
    while (pi.hasNext()) {
      Object elt = pi.nextPosition().element();
      pq.insert(elt,elt);
    }

    pi.reset();
    while (!pq.isEmpty())
      s.replaceElement(pi.nextPosition(),pq.removeMin());
  }

}
