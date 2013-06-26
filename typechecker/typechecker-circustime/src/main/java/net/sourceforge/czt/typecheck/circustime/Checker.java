/*
Copyright (C) 2005, 2006, 2007, 2008 Leo Freitas
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
package net.sourceforge.czt.typecheck.circustime;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.Action1;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circustime.ast.PrefixingTimeAction;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;

public abstract class Checker<R>
  extends net.sourceforge.czt.typecheck.circus.Checker<R>
{
	
  // Needed to check the time expression is of the right (maximal) type
  private final Expr arithmosExpr_;
  //protected final Type2 arithmosType_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    assert typeChecker != null;
    typeChecker_ = typeChecker;
    
    // if arithmos type is wrong somehow, this will catch it.
    // DON'T CACHE arithmos type as it won't work from the beginning.
    arithmosExpr_ = factory().createRefExpr(factory().createZName(ZString.ARITHMOS));
    //arithmosType_ = factory().createPowerType(factory().createGivenType(factory().createZName(ZString.ARITHMOS)));
  }
  
  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object[] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
      sectName(), GlobalDefs.nearestLocAnn(term), markup());
    return errorAnn;
  }
  
  protected void error(Term term, ErrorMessage errorMsg, Object[] params)
  {
    ErrorAnn errorAnn = errorAnn(term, errorMsg, params);
    error(term, errorAnn);
  }

  protected Type2 typeCheckTimeExpr(Term term, Expr expr)
  {
    // whatever the type, even if with generic, it must be at least ARITHMOS
    // this include both \nat and \real for the time of TIME.
    Type2 found = GlobalDefs.unwrapType(expr.accept(exprChecker()));
    Type2 expected = arithmosExpr_.accept(exprChecker());
    
    //if (expected instanceof PowerType)
    //{
      //assert arithmosType_.equals(expected);
    //  expected = ((PowerType)expected).getType();
    //}
    // TODO: debug to see if such unwrapping is needed
    
    // if arithmos type is wrong somehow, this will catch it.
    // DON'T CACHE arithmos type as it won't work from the beginning.
    if (!unify(found, expected).equals(UResult.SUCC))
    {
      Object[] params = {
        getCurrentProcessName(), getCurrentActionName(),
        term.getClass().getSimpleName(), expr, expected, found
      };
      error(term, ErrorMessage.CIRCUS_TIME_EXPR_DONT_UNIFY, params);
    }
  }
}

