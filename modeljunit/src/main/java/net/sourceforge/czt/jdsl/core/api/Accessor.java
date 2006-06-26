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
 * All JDSL core containers provide a way to access their internal structure;
 * <code>Accessor</code> is the interface that embodies this concept.  Containers
 * guarantee not to change the binding between an Accessor and its
 * element, unless the user explicitly requests a change
 * (PositionalContainer.swap(.) and various *Container.replace*(.)
 * are the only methods that change the binding).
 * <p>
 * An Accessor provides only the minimal guarantee of being able to
 * retrieve an element.  All container interfaces are actually written in terms
 * of the two subinterfaces of Accessor:  Position and Locator.
 * PositionalContainers use Positions, and they add topological
 * information (i.e., adjacency information) to the element-binding
 * provided by Accessor.  KeyBasedContainers use Locators, and they
 * add a key to Accessor's element.  
 *
 * @see Position
 * @see Locator
 * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Luca Vismara (lv)
 */
public interface Accessor {

    /** 
     * Gets the element currently associated with this
     * accessor.
     *
     * @return the element currently stored at this accessor
     *
     */
    public Object element();

}
