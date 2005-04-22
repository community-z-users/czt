
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstInterface.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004, 2005 Mark Utting
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

package net.sourceforge.czt.circus.ast;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

/**
 * An action given as a schema expression.
        In this way, schema expressions are included into the Action subtree
        in a similar way as schema expressions are included in the declaration and
        predicat subtrees.
 *
 * @author Gnast version 0.1
 */
public interface SchExprAction extends Action
{

  /**
   * Returns the SchExpr element.
   *
   * @return the SchExpr element.
   */
  net.sourceforge.czt.z.ast.SchExpr getSchExpr();

  /**
   * Sets the SchExpr element.
   *
   * @param schExpr   the SchExpr element.
   * @see #getSchExpr
   */
  void setSchExpr(net.sourceforge.czt.z.ast.SchExpr schExpr);

  /**
   * Returns the IsState element.
   *
   * @return the IsState element.
   */
  Boolean getIsState();

  /**
   * Sets the IsState element.
   *
   * @param isState   the IsState element.
   * @see #getIsState
   */
  void setIsState(Boolean isState);
}
