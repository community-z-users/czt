/*
Copyright 2003 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.base.ast;

import java.util.List;

/**
 * <p>An annotated Z construct/term.</p>
 *
 * <p>Most of the Z terms may have one or more annotations (that is
 * wy it is called an annotated syntax tree).  Annotations are usually
 * used by tools to provide, for instance, type information, location
 * information, ect., but its use is not restricted.  Annotations can
 * be used to attach any type of information to an annotated Z term.</p>
 *
 * <p>Note that annotations are NOT considered as children of a term,
 * that means they are not returned via the {@link #getChildren}-method.</p>
 *
 * @author Petra Malik
 */
public interface TermA extends Term
{
  /**
   * <p>Returns a list of annotations.</p>
   *
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of annotations (should never be <code>null</code>).
   */
  List getAnns();
}
