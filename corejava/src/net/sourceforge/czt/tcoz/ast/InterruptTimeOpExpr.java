
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

package net.sourceforge.czt.tcoz.ast;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;

/**
 *
 * @author Gnast version 0.1
 */
public interface InterruptTimeOpExpr extends Term
{

  /**
   * Returns the NormalOp element.
   *
   * @return the NormalOp element.
   */
  net.sourceforge.czt.oz.ast.OperationExpr getNormalOp();

  /**
   * Sets the NormalOp element.
   *
   * @param normalOp   the NormalOp element.
   * @see #getNormalOp
   */
  void setNormalOp(net.sourceforge.czt.oz.ast.OperationExpr normalOp);

  /**
   * Returns the IntOrTimeout element.
   *
   * @return the IntOrTimeout element.
   */
  net.sourceforge.czt.z.ast.Expr1 getIntOrTimeout();

  /**
   * Sets the IntOrTimeout element.
   *
   * @param intOrTimeout   the IntOrTimeout element.
   * @see #getIntOrTimeout
   */
  void setIntOrTimeout(net.sourceforge.czt.z.ast.Expr1 intOrTimeout);

  /**
   * Returns the HandlerOp element.
   *
   * @return the HandlerOp element.
   */
  net.sourceforge.czt.oz.ast.OperationExpr getHandlerOp();

  /**
   * Sets the HandlerOp element.
   *
   * @param handlerOp   the HandlerOp element.
   * @see #getHandlerOp
   */
  void setHandlerOp(net.sourceforge.czt.oz.ast.OperationExpr handlerOp);
}
