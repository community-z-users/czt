
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstInterface.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.z.ast;

import net.sourceforge.czt.base.ast.*;

/**
 * A (generic) axiomatic paragraph, (generic) schema definition,
        or (generic) horizontal definition
        (C.4.3, C.4.4, C.4.5, C.4.6, C.4.7, C.4.8).
 *
 * @author Gnast version 0.1
 */
public interface AxPara extends Para
{

  /**
   * <p>Returns the DeclName elements.</p>
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of DeclName elements.
   */
  net.sourceforge.czt.base.ast.ListTerm getDeclName();

  /**
   * Returns the SchText element.
   *
   * @return the SchText element.
   */
  SchText getSchText();

  /**
   * Sets the SchText element.
   *
   * @param schText   the SchText element.
   * @see #getSchText
   */
  void setSchText(SchText schText);

  /**
   * Returns the Box element.
   *
   * @return the Box element.
   */
  Box getBox();

  /**
   * Sets the Box element.
   *
   * @param box   the Box element.
   * @see #getBox
   */
  void setBox(Box box);
}
