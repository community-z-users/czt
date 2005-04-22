
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE CoreFactory.vm.
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
   * Creates an instance of {@link JokerName}.
   *
   * @return the new instance of JokerName.
   */
  JokerName createJokerName();

  /**
   * Creates an instance of {@link JokerName} with the given children.
   *
   * @return the new instance of JokerName.
   */
  JokerName createJokerName(String word, java.util.List stroke, String id, String name);

  /**
   * Creates an instance of {@link PredSequent}.
   *
   * @return the new instance of PredSequent.
   */
  PredSequent createPredSequent();

  /**
   * Creates an instance of {@link PredSequent} with the given children.
   *
   * @return the new instance of PredSequent.
   */
  PredSequent createPredSequent(SequentContext sequentContext, net.sourceforge.czt.z.ast.Pred pred, Deduction deduction);

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
   * Creates an instance of {@link JokerExprListBinding}.
   *
   * @return the new instance of JokerExprListBinding.
   */
  JokerExprListBinding createJokerExprListBinding();

  /**
   * Creates an instance of {@link JokerExprListBinding} with the given children.
   *
   * @return the new instance of JokerExprListBinding.
   */
  JokerExprListBinding createJokerExprListBinding(JokerExprList jokerExprList, java.util.List expr);

  /**
   * Creates an instance of {@link JokerExprBinding}.
   *
   * @return the new instance of JokerExprBinding.
   */
  JokerExprBinding createJokerExprBinding();

  /**
   * Creates an instance of {@link JokerExprBinding} with the given children.
   *
   * @return the new instance of JokerExprBinding.
   */
  JokerExprBinding createJokerExprBinding(JokerExpr jokerExpr, net.sourceforge.czt.z.ast.Expr expr);

  /**
   * Creates an instance of {@link LookupConstDeclProviso}.
   *
   * @return the new instance of LookupConstDeclProviso.
   */
  LookupConstDeclProviso createLookupConstDeclProviso();

  /**
   * Creates an instance of {@link LookupConstDeclProviso} with the given children.
   *
   * @return the new instance of LookupConstDeclProviso.
   */
  LookupConstDeclProviso createLookupConstDeclProviso(SequentContext sequentContext, net.sourceforge.czt.z.ast.Expr leftExpr, net.sourceforge.czt.z.ast.Expr rightExpr);

  /**
   * Creates an instance of {@link JokerExprList}.
   *
   * @return the new instance of JokerExprList.
   */
  JokerExprList createJokerExprList();

  /**
   * Creates an instance of {@link JokerExprList} with the given children.
   *
   * @return the new instance of JokerExprList.
   */
  JokerExprList createJokerExprList(String name);

  /**
   * Creates an instance of {@link LookupPredProviso}.
   *
   * @return the new instance of LookupPredProviso.
   */
  LookupPredProviso createLookupPredProviso();

  /**
   * Creates an instance of {@link LookupPredProviso} with the given children.
   *
   * @return the new instance of LookupPredProviso.
   */
  LookupPredProviso createLookupPredProviso(SequentContext sequentContext, net.sourceforge.czt.z.ast.Pred pred);

  /**
   * Creates an instance of {@link CalculateProviso}.
   *
   * @return the new instance of CalculateProviso.
   */
  CalculateProviso createCalculateProviso();

  /**
   * Creates an instance of {@link CalculateProviso} with the given children.
   *
   * @return the new instance of CalculateProviso.
   */
  CalculateProviso createCalculateProviso(SequentContext sequentContext, net.sourceforge.czt.z.ast.Expr leftExpr, net.sourceforge.czt.z.ast.Expr rightExpr);

  /**
   * Creates an instance of {@link SequentContext}.
   *
   * @return the new instance of SequentContext.
   */
  SequentContext createSequentContext();

  /**
   * Creates an instance of {@link JokerNameBinding}.
   *
   * @return the new instance of JokerNameBinding.
   */
  JokerNameBinding createJokerNameBinding();

  /**
   * Creates an instance of {@link JokerNameBinding} with the given children.
   *
   * @return the new instance of JokerNameBinding.
   */
  JokerNameBinding createJokerNameBinding(JokerName jokerName, net.sourceforge.czt.z.ast.DeclName declName);

  /**
   * Creates an instance of {@link Deduction}.
   *
   * @return the new instance of Deduction.
   */
  Deduction createDeduction();

  /**
   * Creates an instance of {@link Deduction} with the given children.
   *
   * @return the new instance of Deduction.
   */
  Deduction createDeduction(java.util.List binding, java.util.List sequent, String name);

  /**
   * Creates an instance of {@link Rule}.
   *
   * @return the new instance of Rule.
   */
  Rule createRule();

  /**
   * Creates an instance of {@link Rule} with the given children.
   *
   * @return the new instance of Rule.
   */
  Rule createRule(java.util.List sequent, String name);

  /**
   * Creates an instance of {@link CheckProviso}.
   *
   * @return the new instance of CheckProviso.
   */
  CheckProviso createCheckProviso();

  /**
   * Creates an instance of {@link CheckProviso} with the given children.
   *
   * @return the new instance of CheckProviso.
   */
  CheckProviso createCheckProviso(SequentContext sequentContext, net.sourceforge.czt.z.ast.Pred pred);

  /**
   * Creates an instance of {@link JokerDeclList}.
   *
   * @return the new instance of JokerDeclList.
   */
  JokerDeclList createJokerDeclList();

  /**
   * Creates an instance of {@link JokerDeclList} with the given children.
   *
   * @return the new instance of JokerDeclList.
   */
  JokerDeclList createJokerDeclList(String name);

  /**
   * Creates an instance of {@link Binding}.
   *
   * @return the new instance of Binding.
   */
  Binding createBinding();

  /**
   * Creates an instance of {@link TypeProviso}.
   *
   * @return the new instance of TypeProviso.
   */
  TypeProviso createTypeProviso();

  /**
   * Creates an instance of {@link TypeProviso} with the given children.
   *
   * @return the new instance of TypeProviso.
   */
  TypeProviso createTypeProviso(SequentContext sequentContext, net.sourceforge.czt.z.ast.Expr expr, net.sourceforge.czt.z.ast.Type type);

  /**
   * Creates an instance of {@link JokerDeclListBinding}.
   *
   * @return the new instance of JokerDeclListBinding.
   */
  JokerDeclListBinding createJokerDeclListBinding();

  /**
   * Creates an instance of {@link JokerDeclListBinding} with the given children.
   *
   * @return the new instance of JokerDeclListBinding.
   */
  JokerDeclListBinding createJokerDeclListBinding(JokerDeclList jokerDeclList, java.util.List decl);

  /**
   * Creates an instance of {@link Jokers}.
   *
   * @return the new instance of Jokers.
   */
  Jokers createJokers();

  /**
   * Creates an instance of {@link Jokers} with the given children.
   *
   * @return the new instance of Jokers.
   */
  Jokers createJokers(java.util.List name, String kind);

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
   * Creates an instance of {@link JokerPredBinding}.
   *
   * @return the new instance of JokerPredBinding.
   */
  JokerPredBinding createJokerPredBinding();

  /**
   * Creates an instance of {@link JokerPredBinding} with the given children.
   *
   * @return the new instance of JokerPredBinding.
   */
  JokerPredBinding createJokerPredBinding(JokerPred jokerPred, net.sourceforge.czt.z.ast.Pred pred);

}
