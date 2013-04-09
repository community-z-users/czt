/*
  Copyright (C) 2007 Leo Freitas
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circustime.ast.TimeEndByProcess;
import net.sourceforge.czt.circustime.ast.TimeStartByProcess;
import net.sourceforge.czt.circustime.ast.TimedinterruptProcess;
import net.sourceforge.czt.circustime.ast.TimeoutProcess;
import net.sourceforge.czt.circustime.visitor.TimeEndByProcessVisitor;
import net.sourceforge.czt.circustime.visitor.TimeStartByProcessVisitor;
import net.sourceforge.czt.circustime.visitor.TimedinterruptProcessVisitor;
import net.sourceforge.czt.circustime.visitor.TimeoutProcessVisitor;
import net.sourceforge.czt.typecheck.circus.ErrorAnn;
import net.sourceforge.czt.typecheck.circustime.ErrorMessage;
import net.sourceforge.czt.typecheck.circustime.ProcessChecker;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.util.ZString;

public class ProcessChecker
extends net.sourceforge.czt.typecheck.circus.ProcessChecker
implements
TimeoutProcessVisitor<CircusCommunicationList>,
TimeStartByProcessVisitor<CircusCommunicationList>,
TimeEndByProcessVisitor<CircusCommunicationList>,
TimedinterruptProcessVisitor<CircusCommunicationList>
{  
private final Expr arithmos_; 
public ProcessChecker(TypeChecker typeChecker)
{
  super(typeChecker);
  arithmos_ = factory().createRefExpr(factory().createZDeclName(ZString.ARITHMOS));
}

@Override
public CircusCommunicationList visitTerm(Term term)
{
  return term.accept(this);
}


@Override
public CircusCommunicationList visitTimedinterruptProcess(
		TimedinterruptProcess term) {
	checkProcessParaScope(term, null);
	CircusCommunicationList commList = visitProcess2(term);
	typeCheckTimeExpr(term, term.getExpr());    
    return commList;
}

@Override
public CircusCommunicationList visitTimeEndByProcess(TimeEndByProcess term) {
	checkProcessParaScope(term, null);
	CircusCommunicationList commList = term.getCircusProcess().accept(processChecker());
	typeCheckTimeExpr(term, term.getExpr());    
    return commList;
}

@Override
public CircusCommunicationList visitTimeStartByProcess(TimeStartByProcess term) {
	checkProcessParaScope(term, null);
	CircusCommunicationList commList = term.getCircusProcess().accept(processChecker());
	typeCheckTimeExpr(term, term.getExpr());    
    return commList;
}

@Override
public CircusCommunicationList visitTimeoutProcess(TimeoutProcess term) {
	CircusCommunicationList commList = visitProcess2(term);
	typeCheckTimeExpr(term, term.getExpr());    
    return commList;
}

protected void typeCheckTimeExpr(Term term, Expr expr)
{
  Type2 found = GlobalDefs.unwrapType(expr.accept(exprChecker()));
  Type2 expected = arithmos_.accept(exprChecker());
  if (expected instanceof PowerType)
  {
    expected = ((PowerType)expected).getType();
  }
  if (!unify(found, expected).equals(UResult.SUCC))
  {
    Object[] params = {
      getCurrentProcessName(), getCurrentActionName(),
      term.getClass().getSimpleName(), expr, expected, found
    };
    ErrorAnn errorAnn = errorAnn(term, ErrorMessage.CIRCUS_TIME_EXPR_DONT_UNIFY, params);
    error(term, errorAnn);
  }
}

private ErrorAnn errorAnn(Term term, ErrorMessage error,
		Object[] params) {
	ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
		    sectName(), GlobalDefs.nearestLocAnn(term), markup());
		  return errorAnn;
}
}

