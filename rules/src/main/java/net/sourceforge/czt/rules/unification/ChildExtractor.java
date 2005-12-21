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
             ZDeclNameVisitor<Object[]>,
             ZRefNameVisitor<Object[]>
{
  private final String DECLLIST = "DeclList";

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
                     axPara.getDeclName(),
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

  /**
   * @czt.todo Fix this!
   */
  public Object[] visitRefExpr(RefExpr refExpr)
  {
    if (refExpr.getMixfix()) {
      return add("RefExpr", refExpr.getChildren());
    }
    // Ignore type expressions when mixfix is false because
    // expressions in sequents maybe typechecked while expressions
    // in rules are not so that they may be missing type expressions.
    // This is a hack!
    return new Object[] { "RefExpr",
                          refExpr.getRefName() };
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

  public Object[] visitZDeclName(ZDeclName zDeclName)
  {
    Object[] children = { zDeclName.getWord(), zDeclName.getStroke() };
    return children;
  }

  /**
   * Doesn't return the Decl child.
   */
  public Object[] visitZRefName(ZRefName zRefName)
  {
    return new Object[] { "ZRefName",
                          zRefName.getWord(),
                          zRefName.getStroke() };
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
