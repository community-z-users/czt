
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE CoreFactory.vm.
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

package net.sourceforge.czt.zpatt.ast;
import net.sourceforge.czt.z.ast.*;

/**
 * <p>The object factory for the AST.
 * This interface contains factory methods
 * for each concrete Z term.</p>
 *
 * <p>This object factory allows the programmer to programatically
 * construct new instances of concrete Z terms.
 * There is a factory method that does not require arguments
 * (called default factory method)
 * and a factory method where all the children (except annotations)
 * of that particular Z term can be provided.</p>
 *
 * @author Gnast version 0.1
 */
public interface ZpattFactory
  extends net.sourceforge.czt.z.ast.ZFactory
{
  /**
   * Creates an instance of {@link JokerExpr}.
   *
   * @return the new instance of JokerExpr.
   */
  JokerExpr createJokerExpr();

  /**
   * Creates an instance of {@link JokerExpr} with the given children.
   *
   * @return the new instance of JokerExpr.
   */
  JokerExpr createJokerExpr(String name);

  /**
   * Creates an instance of {@link Substitute}.
   *
   * @return the new instance of Substitute.
   */
  Substitute createSubstitute();

  /**
   * Creates an instance of {@link Substitute} with the given children.
   *
   * @return the new instance of Substitute.
   */
  Substitute createSubstitute(java.util.List expr, java.util.List pred);

  /**
   * Creates an instance of {@link JokerPred}.
   *
   * @return the new instance of JokerPred.
   */
  JokerPred createJokerPred();

  /**
   * Creates an instance of {@link JokerPred} with the given children.
   *
   * @return the new instance of JokerPred.
   */
  JokerPred createJokerPred(String name);

  /**
   * Creates an instance of {@link SubstList}.
   *
   * @return the new instance of SubstList.
   */
  SubstList createSubstList();

  /**
   * Creates an instance of {@link SubstList} with the given children.
   *
   * @return the new instance of SubstList.
   */
  SubstList createSubstList(java.util.List substitute);

}
