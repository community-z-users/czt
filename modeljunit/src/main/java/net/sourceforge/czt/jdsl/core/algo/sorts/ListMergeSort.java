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
 * Performs a merge-sort in O(n log n) time, provided that isEmpty(),
 * first(), insertLast(), and removeFirst() all operate in O(1) time.
 *
 * @author Benoit Hudson
 * @author Roberto Tamassia
 * @author Luca Vismara
 * @author Keith Schmidt
 * @version JDSL 2.1.1 
 */
public class ListMergeSort implements SortObject {

  
  /** 
   * Recursively divides a Sequence into (roughly) equal subsequences
   * and merges them back together once sorted.
   *
   * @param S the sequence to sort
   * @param c the comparator to use in the sort 
   */
  public void sort(Sequence S, Comparator c) {

    int n = S.size();
    if (n > 1) {

      // divide
      Sequence S1 = (Sequence)S.newContainer();
      for (int i=1; i <= (n+1)/2; i++) {
	S1.insertLast(S.removeFirst());
      }
      Sequence S2 = (Sequence)S.newContainer();
      for (int i=1; i <= n/2; i++) {
	S2.insertLast(S.removeFirst());
      }

      // recur
      sort(S1,c);
      sort(S2,c);

      //conquer
      merge(S1,S2,c,S);
    }
  }

  
  /** 
   * Merges two sequences.
   * This is done by taking the lower of the two sequence's first
   * elements off the appropriate sequence and into the sequence to
   * return.  This is done until one of the sequences is empty, at which
   * point the remainder of the other sequence is appended, and the
   * sequence returned.  Note that in this implementation, S1 and S2 are
   * destroyed.  
   *
   * @param S1 the first sequence to merge
   * @param S2 the second sequence to merge
   * @param c the comparator to use
   * @param S the sequence that will store the merge of S1 and S2
   */
  private void merge(Sequence S1, Sequence S2, Comparator c, Sequence S) {

    while(!S1.isEmpty() && !S2.isEmpty()) {
      if(c.isLessThan(S1.first().element(),S2.first().element())) {
	S.insertLast(S1.removeFirst());
      }
      else {
	S.insertLast(S2.removeFirst());
      }
    }

    while(!S2.isEmpty()) {
      S.insertLast(S2.removeFirst());
      }

    while(!S1.isEmpty()) {
      S.insertLast(S1.removeFirst());
    }
  }


}
