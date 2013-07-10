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

import net.sourceforge.czt.circus.ast.Action1;
import net.sourceforge.czt.circus.ast.Action2;
import net.sourceforge.czt.circus.ast.ActionIte;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelAction;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelActionIte;
import net.sourceforge.czt.circus.ast.BasicAction;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommand;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.HideAction;
import net.sourceforge.czt.circus.ast.InterleaveAction;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.ParActionIte;
import net.sourceforge.czt.circus.ast.ParallelAction;
import net.sourceforge.czt.circus.ast.ParallelActionIte;
import net.sourceforge.czt.circus.ast.ParamAction;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.RenameAction;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.SubstitutionAction;
import net.sourceforge.czt.circus.visitor.Action1Visitor;
import net.sourceforge.czt.circus.visitor.Action2Visitor;
import net.sourceforge.czt.circus.visitor.ActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.BasicActionVisitor;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.CircusCommandVisitor;
import net.sourceforge.czt.circus.visitor.GuardedActionVisitor;
import net.sourceforge.czt.circus.visitor.HideActionVisitor;
import net.sourceforge.czt.circus.visitor.InterleaveActionVisitor;
import net.sourceforge.czt.circus.visitor.MuActionVisitor;
import net.sourceforge.czt.circus.visitor.ParActionIteVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.ParamActionVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.RenameActionVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus.visitor.SubstitutionActionVisitor;
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
		PrefixingTimeActionVisitor<CircusCommunicationList>,
		 ParamActionVisitor<CircusCommunicationList>,                  //  C.12.1, C.12.2, C.16.1
		  SchExprActionVisitor<CircusCommunicationList>,                //  C.12.3
		  CallActionVisitor<CircusCommunicationList>,                   //  C.12.4, C.12.19, C.12.20, C.17.6
		  CircusCommandVisitor<CircusCommunicationList>,                //  C.12.5
		  BasicActionVisitor<CircusCommunicationList>,
		  //SkipActionVisitor,                                      C.12.6
		  //StopActionVisitor,                                      C.12.7
		  //ChaosActionVisitor,                                     C.12.8
		  SubstitutionActionVisitor<CircusCommunicationList>,           //  C.12.9     
		  PrefixingActionVisitor<CircusCommunicationList>,              //  C.12.10
		  GuardedActionVisitor<CircusCommunicationList>,                //  C.12.11
		  Action2Visitor<CircusCommunicationList>,
		  //SeqActionVisitor,                                       C.12.12
		  //InterruptActionVisitor,
		  //ExtChoiceActionVisitor,                                 C.12.13
		  //IntChoiceActionVisitor,                                 C.12.14  
		  InterleaveActionVisitor<CircusCommunicationList>,             //  C.12.15, C.12.16
		  ParallelActionVisitor<CircusCommunicationList>,               //  C.12.17
		  AlphabetisedParallelActionVisitor<CircusCommunicationList>,   //  C.12.17-2
		  
		  Action1Visitor<CircusCommunicationList>,
		  HideActionVisitor<CircusCommunicationList>,                   //  C.12.18
		  RenameActionVisitor<CircusCommunicationList>,                 //  NEW
		  MuActionVisitor<CircusCommunicationList>,                     //  C.12.21
		  ActionIteVisitor<CircusCommunicationList>,                      
		  //SeqActionIteVisitor,                                    C.12.22
		  //ExtChoiceActionIteVisitor,                              C.12.23
		  //IntChoiceActionIteVisitor,                              C.12.24  
		  ParActionIteVisitor<CircusCommunicationList>,                 //  C.12.25, C.12.26
		  ParallelActionIteVisitor<CircusCommunicationList>,            //  C.12.27
		  AlphabetisedParallelActionIteVisitor<CircusCommunicationList>//  C.12.27-2

		

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

	@Override
	public CircusCommunicationList visitAlphabetisedParallelActionIte(
			AlphabetisedParallelActionIte term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitParallelActionIte(ParallelActionIte term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitParActionIte(ParActionIte term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitActionIte(ActionIte term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitMuAction(MuAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitRenameAction(RenameAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitHideAction(HideAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitAction1(Action1 term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitAlphabetisedParallelAction(
			AlphabetisedParallelAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitParallelAction(ParallelAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitInterleaveAction(InterleaveAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitAction2(Action2 term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitGuardedAction(GuardedAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitPrefixingAction(PrefixingAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitSubstitutionAction(
			SubstitutionAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitBasicAction(BasicAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitCircusCommand(CircusCommand term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitCallAction(CallAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitSchExprAction(SchExprAction term) {
		return term.accept(circusActionChecker_);
	}

	@Override
	public CircusCommunicationList visitParamAction(ParamAction term) {
		return term.accept(circusActionChecker_);
	}

}
