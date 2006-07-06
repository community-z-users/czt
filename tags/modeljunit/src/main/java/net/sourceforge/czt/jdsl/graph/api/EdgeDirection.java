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

/**
 * Interface containing constants for specifying which edges are desired in
 * graph-query methods.
 * Note that constants can be OR'd together in any combination:
 * <code>IN | OUT</code> specifies all directed edges, etc.
 *
 * Note that you can implement this interface to get notationally
 * convenient access to the names of the constants.  For instance,
 * an algorithm class could implement this interface
 * and refer to the constants as <code>IN</code> rather than
 * <code>EdgeDirection.IN</code>, etc.  
 *
 * @version JDSL 2.1.1 
 * @author Mark Handy
 */
public interface EdgeDirection {

    public static final int IN = 1;
    public static final int OUT = 2;
    public static final int UNDIR = 4;

}
