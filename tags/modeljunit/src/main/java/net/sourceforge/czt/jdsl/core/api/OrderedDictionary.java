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
  * A Dictionary in which the keys are totally ordered. That is, given a set of
  * keys, <I>S</I>, where <I>a</I> and <I>b</I> are elements of <I>S</I>,
  * exactly one of the following properties holds:
  * <UL>
  *     <LI> <I>a</I> &lt; <I>b</I>
  *     <LI> <I>a</I> = <I>b</I>
  *     <LI> <I>a</I> &gt; <I>b</I>
  * </UL>
  * This extension of the concept of a dictionary allows ordered dictionaries to
  * be traversed through sequentially; the order is guaranteed to be the order
  * of the keys (except that no order is guaranteed for equal keys).
  *
  * @version JDSL 2.1.1 
  *
  * @see InspectableOrderedDictionary
  * @see Dictionary
  *
 * @author Mark Handy
 * @author Luca Vismara
 * @author Andrew Schwerin
  */

public interface OrderedDictionary 
  extends InspectableOrderedDictionary, Dictionary {

}
