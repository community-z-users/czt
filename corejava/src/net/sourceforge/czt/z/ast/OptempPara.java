
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
 * An operator template paragraph (C.4.13). This contains a list 
        of at least two Oper elements.  In fact, Oper has two subtypes
        (Operand and Operator) and the list must alternate between these.
        In other words, every Operand must be followed by an Operator
        (unless it is the last element in the list) and every Operator
        must be followed by an Operand (unless it is the last in the list).
        For example, an infix operator like '+' would be defined by
        Operand, Operator with Word="+", Operand.
 *
 * @author Gnast version 0.1
 */
public interface OptempPara extends Para
{

  /**
   * <p>Returns the Oper elements.</p>
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of Oper elements.
   */
  net.sourceforge.czt.base.ast.ListTerm getOper();

  /**
   * Returns the Cat element.
   *
   * @return the Cat element.
   */
  Cat getCat();

  /**
   * Sets the Cat element.
   *
   * @param cat   the Cat element.
   * @see #getCat
   */
  void setCat(Cat cat);

  /**
   * Returns the Assoc element.
   *
   * @return the Assoc element.
   */
  Assoc getAssoc();

  /**
   * Sets the Assoc element.
   *
   * @param assoc   the Assoc element.
   * @see #getAssoc
   */
  void setAssoc(Assoc assoc);

  /**
   * Returns the Prec element.
   *
   * @return the Prec element.
   */
  Integer getPrec();

  /**
   * Sets the Prec element.
   *
   * @param prec   the Prec element.
   * @see #getPrec
   */
  void setPrec(Integer prec);
}
