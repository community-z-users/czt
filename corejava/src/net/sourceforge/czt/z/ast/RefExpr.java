
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

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
package net.sourceforge.czt.z.ast;

import net.sourceforge.czt.base.ast.*;

/**
 * 
        A reference expression (C.6.21, C.6.28, C.6.29).
	<ul>
	<li>C.6.21 (Generic Operator Application).  For example: S \rel T.
		In this case, mixfix is always true and the list of 
		type expressions is non-empty (it contains [S,T]).</li>
	<li>C.6.28 (Reference).  For example: \emptyset.
		In this case, mixfix is always false and the list of 
		type expressions is empty.</li>
	<li>C.6.29 (Generic Instantiation).  For example: \emptyset[T].
		In this case, mixfix is always false and the list of 
		type expressions is non-empty (it contains [T]).</li>
	</ul>
      
 *
 * @author Gnast version 0.1
 */
public interface RefExpr extends Expr
{

  /**
   * Returns the RefName element.
   *
   * @return the RefName element.
   */
  RefName getRefName();

  /**
   * Sets the RefName element.
   *
   * @param refName   the RefName element.
   * @see #getRefName
   */
  void setRefName(RefName refName);

  /**
   * <p>Returns the Expr elements.</p>
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of Expr elements.
   */
  java.util.List getExpr();

  /**
   * Returns the Mixfix element.
   *
   * @return the Mixfix element.
   */
  Boolean getMixfix();

  /**
   * Sets the Mixfix element.
   *
   * @param mixfix   the Mixfix element.
   * @see #getMixfix
   */
  void setMixfix(Boolean mixfix);
}
