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
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circustime.ast.ProcessTime1;
import net.sourceforge.czt.circustime.ast.ProcessTime2;
import net.sourceforge.czt.circustime.visitor.ProcessTime1Visitor;
import net.sourceforge.czt.circustime.visitor.ProcessTime2Visitor;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;

public class ProcessChecker extends Checker<CircusCommunicationList> implements
		ProcessTime2Visitor<CircusCommunicationList>,
		ProcessTime1Visitor<CircusCommunicationList> {

	// a Circus process checker
	protected net.sourceforge.czt.typecheck.circus.ProcessChecker circusProcessChecker_;

	public ProcessChecker(TypeChecker typeChecker) {
		super(typeChecker);
		circusProcessChecker_ = new net.sourceforge.czt.typecheck.circus.ProcessChecker(
				typeChecker);
	}

	/**
	 * For all other Process terms, use the standard Circus typechecking rules
	 * within the checking environment for CircusTime.
	 */

	public CircusCommunicationList visitTerm(Term term) {
		return term.accept(circusProcessChecker_);
	}

	protected CircusCommunicationList typeCheckProcessTimeExpr(
			CircusProcess term, Expr expr) {
		assert expr != null && term != null;
		checkProcessParaScope(term, null);
		typeCheckTimeExpr(term, expr);
		// we want to fall back to the Circus process checker, which will catch
		// this production as either Process1/2.
		return term.accept(circusProcessChecker_);
	}

	@Override
	public CircusCommunicationList visitProcessTime1(ProcessTime1 term) {
		return typeCheckProcessTimeExpr(term, term.getExpr());
	}

	@Override
	public CircusCommunicationList visitProcessTime2(ProcessTime2 term) {
		return typeCheckProcessTimeExpr(term, term.getExpr());
	}
}
