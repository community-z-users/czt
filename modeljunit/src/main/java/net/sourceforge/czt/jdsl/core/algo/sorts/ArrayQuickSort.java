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
 * Performs an in-place quicksort in expected O(n log n)
 * time, provided that the atRank(int) method of the Sequence operates in
 * O(1) time. The worst-case sort time is O(n-squared).  The partition
 * element is deterministically chosen to be the
 * first element of the subsequence being sorted.
 *
 * @author Mark Handy
 * @author Benoit Hudson
 * @author Keith Schmidt
 * @version JDSL 2.1.1 
 */
public class ArrayQuickSort implements SortObject {
    private Sequence S;
    private Comparator c;
  
    public void sort (Sequence S, Comparator c) {
        this.S = S; this.c = c;
        qsort(0, S.size()-1);
    }

    /**
     * Partition the sequence, and recursively sort the two
     * subsequences on either side of the partition element.
     *
     * @param p    the index of the start of the subsequence to be
     *                 sorted.  
     * @param r    the index of the end of the subsequence to be
     *                 sorted.  
     */
    private final void qsort(int p, int r) {
        if(p<r) {
            int q = partition(p,r);
            qsort(q+1,r);
            qsort(p,q);
        } // else we're done
    }

    /**
     * Choose the partition element.
     *
     * Iterate along the Sequence swapping two elements whenever the
     * element of higher rank is less than the partition element and
     * the element of lower rank is greater than the partitition
     * element.
     *
     * @param p    the index of the start of the subsequence to be
     *                 sorted.  
     * @param r    the index of the end of the subsequence to be
     *                 sorted.  
     */
    private final int partition(int p, int r) {
        Object x = S.atRank(p).element();
        int i = p-1;
        int j = r+1;
        while(true) {
            do { j--; } while(c.compare(S.atRank(j).element(),x)>0);
            do { i++; } while(c.compare(S.atRank(i).element(),x)<0);
            if(i<j) {
                S.swapElements(S.atRank(i),S.atRank(j));
            } else return j;
        }
    }

}
