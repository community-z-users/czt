/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.rules.unification;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * <p>A visitor that extracts the children of a given term suitable for
 * unification.</p>
 *
 * @author Petra Malik
 */
public class ChildExtractor
  implements ApplExprVisitor<Object[]>,
             AxParaVisitor<Object[]>,
             HeadDeclListVisitor<Object[]>,
             MemPredVisitor<Object[]>,
             RefExprVisitor<Object[]>,
             TermVisitor<Object[]>,
             ZDeclListVisitor<Object[]>,
             ZNameVisitor<Object[]>
{
  private final String DECLLIST = "DeclList";

  private ProverFactory proverFactory_ = new ProverFactory();

  /** Used to allocate unique joker names. */
  private static int typeCounter_ = 1;

  /**
   * Doesn't return the Mixfix child.
   */
  public Object[] visitApplExpr(ApplExpr applExpr)
  {
    Object[] erg = { "ApplExpr",
                     applExpr.getLeftExpr(),
                     applExpr.getRightExpr()};
    return erg;
  }

  /**
   * Doesn't return the Box child.
   */
  public Object[] visitAxPara(AxPara axPara)

  {
    Object[] erg = { "AxPara",
                     axPara.getName(),
                     axPara.getSchText() };
    return erg;
  }

  public Object[] visitHeadDeclList(HeadDeclList headDeclList)
  {
    return new Object[] { DECLLIST, headDeclList };
  }

  /**
   * Doesn't return the Mixfix child.
   */
  public Object[] visitMemPred(MemPred memPred)
  {
    Object[] erg = { "MemPred",
                     memPred.getLeftExpr(),
                     memPred.getRightExpr()};
    return erg;
  }

  /** Returns the name and type parameters of refExpr.
   *  This ignores the mixfix flag.
   *  The existing type parameters are returned unchanged (so must unify)
   *  if refExpr has (a) been typechecked (ie. has a TypeAnn), 
   *  or (b) has explicit=true
   *  or (c) does not have an empty list of type parameters.
   *  Otherwise, the type parameters are assumed to be unknown,
   *  so the default empty list is replaced by a fresh ExprList joker,
   *  which allows it to unify with any other list of expressions.
   */
  public Object[] visitRefExpr(RefExpr refExpr)
  {
    TypeAnn typed = refExpr.getAnn(TypeAnn.class);
    ExprList types = refExpr.getExprList();
    if (typed == null && ! refExpr.getExplicit().booleanValue()
        && types instanceof ZExprList 
        && ((ZExprList)types).isEmpty())
      types = proverFactory_.createJokerExprList("_T"+(typeCounter_ ++), null);
    return new Object[]
       {"RefExpr",
        refExpr.getName(),
        types};
  }

  public Object[] visitTerm(Term term)
  {
    if (term instanceof Wrapper) {
      Wrapper wrapper = (Wrapper) term;
      return wrapper.getChildren();
    }
    else {
      return add(term.getClass().getName(), term.getChildren());
    }
  }

  public Object[] visitZDeclList(ZDeclList zDeclList)
  {
    return new Object[] { DECLLIST, zDeclList };
  }

  /**
   * Doesn't return the Decl child.
   */
  public Object[] visitZName(ZName zName)
  {
    return new Object[] { "ZName",
                          zName.getWord(),
                          zName.getStrokeList() };
  }

  private Object[] add(String name, Object[] children)
  {
    Object[] result = new Object[children.length + 1];
    result[0] = name;
    for (int i = 0; i < children.length; i++) {
      result[i + 1] = children[i];
    }
    return result;
  }
}
