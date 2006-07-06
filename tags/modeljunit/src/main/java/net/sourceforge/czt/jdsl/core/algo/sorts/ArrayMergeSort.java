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
 * Performs a merge-sort in O(n log n) time, provided that the
 * atRank(int) method of the Sequence works in O(1) time. <P>
 * 
 * @author Benoit Hudson
 * @author Keith Schmidt
 * @version JDSL 2.1.1 
 */
public class ArrayMergeSort implements SortObject {
  public void sort(Sequence S, Comparator c) {
    mergeSortHelper(S, 0, (S.size()-1), c) ;
  }
    
  /** 
    * Recursively divides a Sequence into (roughly) equal subsequences
    * and merges them back together once sorted.
    *
    * @param S     the sequence of which to merge subsequences
    * @param start the first index of the subsequence
    * @param end   the last index of the subsequence
    * @param c     the comparator to use 
    */
  private void mergeSortHelper(Sequence S, int start, int end,
			       Comparator c) {
    if(start<end) {
      int middle = (start+end)/2;
      mergeSortHelper(S, start, middle, c) ;
      mergeSortHelper(S, middle+1, end, c) ;
      merge(S, start, middle, end, c);
    }
    // else already sorted (just one or 0 elements)
  }

  /** 
    * Merges the two adjacent (and hopefully sorted) subsequences.<P>
    * Uses O(n) space.
    * @param S    the sequence of which to merge subsequences
    * @param p    the first index of the first subsequence
    * @param q    the last index of the first subsequence
    * @param r    the last index of the second subsequence
    * @param c    the comparator to use
    */
  private void merge(Sequence S, int p, int q, int r, Comparator c) {
    // create temporary storage, initialize it to nulls to make space,
    // and take the subsequences out of S (swap to avoid resizing,
    // a costly operation in an array-based Sequence)
    Sequence S1 = (Sequence)S.newContainer() ;
    Sequence S2 = (Sequence)S.newContainer() ;

    for(int i=p; i<=q; i++) {
      S1.insertLast((S.atRank(i)).element());
    }
    for(int i=q+1; i<=r; i++) {
      S2.insertLast((S.atRank(i)).element());
    }

    // merge the two, replacing the elements in S with the sorted
    // subsequence
    int S1index = 0;
    int S2index = 0;
    int Sindex  = p;
    for(;;) { // loop breaks when one of S1 or S2 is emptied
      if(c.isLessThan(S1.atRank(S1index).element(),
		      S2.atRank(S2index).element())) {

	S.replaceElement(S.atRank(Sindex), 
			 (S1.atRank(S1index)).element());
	S1index++; 
	Sindex++;
	if(S1index >= S1.size()) 
	  break; // S1 now emptied
      }
      else { // S1>=S2
	S.replaceElement(S.atRank(Sindex), 
			 (S2.atRank(S2index)).element());
	S2index++; 
	Sindex++;
	if(S2index >= S2.size()) 
	  break; // S2 now emptied
      }
    }

    // swap what's left into S (only one of these two will run)
    while(S1index<S1.size()) {

      S.replaceElement(S.atRank(Sindex), 
		       (S1.atRank(S1index)).element());
      S1index++; 
      Sindex++;
    }
    while(S2index<S2.size()) {

      S.replaceElement(S.atRank(Sindex), 
		       (S2.atRank(S2index)).element());
      S2index++; 
      Sindex++;
    }
    // all done!
  }
}
