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
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circustime.ast.PrefixingTimeAction;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.util.ZString;

public abstract class Checker<R> extends
		net.sourceforge.czt.typecheck.circus.Checker<R> {

	// Needed to check the time expression is of the right (maximal) type
	private final Expr arithmosExpr_;

	// protected final Type2 arithmosType_;

	public Checker(TypeChecker typeChecker) {
		super(typeChecker);
		assert typeChecker != null;
		typeChecker_ = typeChecker;

		// if arithmos type is wrong somehow, this will catch it.
		// DON'T CACHE arithmos type as it won't work from the beginning.
		arithmosExpr_ = factory().createRefExpr(
				factory().createZName(ZString.ARITHMOS));
		// arithmosType_ =
		// factory().createPowerType(factory().createGivenType(factory().createZName(ZString.ARITHMOS)));
	}

	protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object[] params) {
		ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
				sectName(), GlobalDefs.nearestLocAnn(term), markup());
		return errorAnn;
	}

	protected void error(Term term, ErrorMessage errorMsg, Object[] params) {
		ErrorAnn errorAnn = errorAnn(term, errorMsg, params);
		error(term, errorAnn);
	}

	protected Type2 typeCheckTimeExpr(Term term, Expr expr) {
		// whatever the type, even if with generic, it must be at least ARITHMOS
		// this include both \nat and \real for the time of TIME.
		Type2 found = GlobalDefs.unwrapType(expr.accept(exprChecker()));
		Type2 expected = arithmosExpr_.accept(exprChecker());

		// if (expected instanceof PowerType)
		// {
		// assert arithmosType_.equals(expected);
		// expected = ((PowerType)expected).getType();
		// }
		// TODO: debug to see if such unwrapping is needed

		// if arithmos type is wrong somehow, this will catch it.
		// DON'T CACHE arithmos type as it won't work from the beginning.
		if (!unify(found, expected).equals(UResult.SUCC)) {
			Object[] params = { getCurrentProcessName(),
					getCurrentActionName(), term.getClass().getSimpleName(),
					expr, expected, found };
			error(term, ErrorMessage.CIRCUS_TIME_EXPR_DONT_UNIFY, params);
		}

		return expected;
	}

	/**
	 * For Circus, this just typechecks the following action from a prefix.
	 * Extensions could do more before hand. It assumes an action para scope as
	 * well as scope for input variables. If input variables scope isn't in
	 * place, they won't be visible to the given action.
	 * 
	 * @param term
	 * @return
	 */
	protected CircusCommunicationList typeCheckPrefixFollowingAction(
			Action1 term, List<NameTypePair> inputVars) {
		CircusCommunicationList result = null;
		if (term instanceof PrefixingTimeAction) {
			PrefixingTimeAction pta = (PrefixingTimeAction) term;

			// enter scope for variable name @N. If not in place, it will be an
			// empty scope
			typeEnv().enterScope();

			// check each kind of prefixing time action by typechecking th4e
			// appropriate expressions. ATTIME is just arithmos, and the others
			// call the inner method.
			final Type2 atTimeType;
			if (pta.isAtPrefixingAction()) {
				atTimeType = arithmosExpr_.accept(exprChecker());
			} else if (pta.isPrefixingExprAction()) {
				atTimeType = null;
				typeCheckTimeExpr(pta, pta.getExpr());
			} else if (pta.isAtPrefixingExprAction()) {
				atTimeType = arithmosExpr_.accept(exprChecker());
				typeCheckTimeExpr(pta, pta.getExpr());
			} else {
				atTimeType = null;
				error(pta, ErrorMessage.CIRCUS_TIME_UNKNOWN_PREFIXTIMEACTION,
						new Object[] { getCurrentProcessName(),
								getCurrentActionName(),
								pta.getClass().getSimpleName() });
			}

			// if we do have an explicit ATTIME, add it as a pair to the type
			// environment visible for the following action
			if (atTimeType != null) {
				inputVars.add(factory().createNameTypePair(
						pta.getChannelElapsedTimeDeclName(), atTimeType));

				// TODO: check if need to say
				// typeEnv.addPair(factory().createNameTypePair(pta.getChannelElapsedTime(),
				// atTimeType));

			}

			// typecheck it with possibly @N in scope as in Circus
			result = super.typeCheckPrefixFollowingAction(term, inputVars);

			// close the @N scope
			typeEnv().exitScope();
		} else {
			result = super.typeCheckPrefixFollowingAction(term, inputVars);
		}
		return result;
	}

	protected void adjustPrefixActionSignature(List<NameTypePair> inputVars,
		Communication comm, CircusCommunicationList commList) {
		checkActionSignature(comm);

		// updates the local variable signature for the prefixed action.
		getCurrentActionSignature().getLocalVars().getNameTypePair().addAll(inputVars);

		// add the channels used channels
		GlobalDefs.addNoDuplicates(0, commChecker().lastUsedChannelDecl(),
		getCurrentActionSignature().getUsedChannels().getNameTypePair());

		// add the communication expressions!
		// GlobalDefs.addNoDuplicates(0, comm,
		// actionSignature_.getUsedCommunications());
		GlobalDefs.addNoDuplicates(0, comm, commList);
	}
	
}