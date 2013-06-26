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

import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circustime.visitor.ActionTime2Visitor;
import net.sourceforge.czt.circustime.ast.ActionTime1;
import net.sourceforge.czt.circustime.ast.ActionTime2;
import net.sourceforge.czt.circustime.ast.PrefixingTimeAction;
import net.sourceforge.czt.circustime.ast.WaitAction;
import net.sourceforge.czt.circustime.ast.WaitExprAction;
import net.sourceforge.czt.circustime.visitor.ActionTime1Visitor;
import net.sourceforge.czt.circustime.visitor.PrefixingTimeActionVisitor;
import net.sourceforge.czt.circustime.visitor.WaitActionVisitor;
import net.sourceforge.czt.circustime.visitor.WaitExprActionVisitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Type2;

public class ActionChecker extends Checker<CircusCommunicationList> implements
		WaitActionVisitor<CircusCommunicationList>,
		WaitExprActionVisitor<CircusCommunicationList>,
		ActionTime1Visitor<CircusCommunicationList>,
		ActionTime2Visitor<CircusCommunicationList>,
		PrefixingTimeActionVisitor<CircusCommunicationList>

// Add Action Visitor for each circus time action
{
	protected net.sourceforge.czt.typecheck.circus.ActionChecker circusActionChecker_;

	/** Creates a new instance of ActionChecker */
	public ActionChecker(TypeChecker typeChecker) {
		super(typeChecker);
		circusActionChecker_ = new net.sourceforge.czt.typecheck.circus.ActionChecker(typeChecker);
	}
	
	protected CircusCommunicationList typeCheckActionTimeExpr(CircusAction term, Expr expr) 
	{
		assert expr != null && term != null;
		checkActionParaScope(term);
		typeCheckTimeExpr(term, expr);
		// do not call visit(term) here because we want to fall
		// back to the Circus action checker, which will catch
		// this production as either Action1/2, which then will
		// call visit(term).
		return term.accept(circusActionChecker_);
	}
	
	@Override
	public CircusCommunicationList visitWaitAction(WaitAction term) {
		return typeCheckActionTimeExpr(term, term.getExpr());
	}

	@Override
	public CircusCommunicationList visitWaitExprAction(WaitExprAction term) {
		checkActionParaScope(term, null);
		
		// enter in scope
		typeEnv().enterScope();
		
		// the wait expression can only be unified with arithmos
		Type2 expected = typeCheckTimeExpr(term, term.getExpr());
		
		// create a new name type pair to be in the scope of the timed action
		NameTypePair pair = factory().createNameTypePair(term.getName(), expected);
		typeEnv().add(pair);
		
		// make sure to call visit instead of accept, as it takes care of
		// possibly recursive calls as the ensuing action.
		CircusCommunicationList commList = visit(term.getCircusAction());
		
		// close the scope
		typeEnv().exitScope();
		
		return commList;
	}
	
	@Override
	public CircusCommunicationList visitActionTime2(ActionTime2 term) {
		return typeCheckActionTimeExpr(term, term.getExpr());
	}

	@Override
	public CircusCommunicationList visitActionTime1(ActionTime1 term) {
		return typeCheckActionTimeExpr(term, term.getExpr());
	}

	@Override
	public CircusCommunicationList visitPrefixingTimeAction(PrefixingTimeAction term) {
		return typeCheckPrefixingAction(term, term.getCommunication());
	}
}
