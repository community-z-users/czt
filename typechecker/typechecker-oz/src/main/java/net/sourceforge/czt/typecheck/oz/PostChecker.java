/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;

/**
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined.
 */
public class PostChecker
  extends Checker<net.sourceforge.czt.typecheck.z.ErrorAnn>
  implements BindSelExprVisitor<net.sourceforge.czt.typecheck.z.ErrorAnn>
{
  protected net.sourceforge.czt.typecheck.z.PostChecker zPostChecker_;

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPostChecker_ =
      new net.sourceforge.czt.typecheck.z.PostChecker(typeChecker);
  }

  public net.sourceforge.czt.typecheck.z.ErrorAnn visitTerm(Term term)
  {
    return term.accept(zPostChecker_);
  }

  public ErrorAnn visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    ParameterAnn pAnn = (ParameterAnn) bindSelExpr.getAnn(ParameterAnn.class);
    if (pAnn != null) {
      List<Type2> gParams = pAnn.getParameters();
      for (Type2 type : gParams) {
        try {
          type.accept(carrierSet());
        }
        catch (UndeterminedTypeException e) {
          Object [] params = {bindSelExpr};
          ErrorAnn errorAnn =
            errorAnn(bindSelExpr, ErrorMessage.PARAMETERS_NOT_DETERMINED, params);
          boolean added = addErrorAnn(bindSelExpr, errorAnn);
          removeAnn(bindSelExpr, pAnn);
          return added ? errorAnn : null;
        }
      }
      removeAnn(bindSelExpr, pAnn);
    }
    return null;
  }
}
