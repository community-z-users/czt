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

/**
 * Algorithm interface for sorting a sequence according to a given
 * comparator of elements.  All sorting algorithms are expected to
 * modify the Sequence passed in as a parameter (no new Sequence is
 * returned). No guarantee is made that the Position-element binding
 * is preserved, or even that positions and their decorations are preserved.
 * <p>
 * If the comparator encounters an element which it is unable to compare, a
 * ClassCastException will be thrown, as is documented in the
 * EqualityComparator and Comparator interfaces in net.sourceforge.czt.jdsl.core.api.
 * <p>
 * Running times (time complexities) given for individual algorithms
 * depend on the assumption that the comparator can compare two 
 * elements in constant time.
 *
 * @author Benoit Hudson
 * @author Keith Schmidt
 * @version JDSL 2.1.1 
 */
public interface SortObject {

  /**
   * Method that actually sorts the sequence, with the first element
   * after the sort being the one that the comparator reported was smallest.
   *
   * @param s sequence to be sorted
   * @param c comparator which defines in which order S is sorted
   */
  public void sort(Sequence s, Comparator c);

}
