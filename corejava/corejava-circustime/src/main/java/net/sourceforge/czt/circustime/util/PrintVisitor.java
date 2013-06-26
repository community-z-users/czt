/*
Copyright (C) 2006 Mark Utting
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
package net.sourceforge.czt.circustime.util;

import net.sourceforge.czt.circustime.ast.PrefixingTimeAction;
import net.sourceforge.czt.circustime.ast.TimeEndByAction;
import net.sourceforge.czt.circustime.ast.TimeEndByProcess;
import net.sourceforge.czt.circustime.ast.TimeStartByAction;
import net.sourceforge.czt.circustime.ast.TimeStartByProcess;
import net.sourceforge.czt.circustime.ast.TimedInterruptAction;
import net.sourceforge.czt.circustime.ast.TimedInterruptProcess;
import net.sourceforge.czt.circustime.ast.TimeoutAction;
import net.sourceforge.czt.circustime.ast.TimeoutProcess;
import net.sourceforge.czt.circustime.ast.WaitAction;
import net.sourceforge.czt.circustime.ast.WaitExprAction;
import net.sourceforge.czt.circustime.visitor.CircusTimeVisitor;

/**
 * @author Leo Freitas
 */
public class PrintVisitor
  extends net.sourceforge.czt.circus.util.PrintVisitor
  implements CircusTimeVisitor<String>
{
	@Override
	public String visitTimeoutProcess(TimeoutProcess term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getLeftProcess()));
		result.append("[>");
		result.append(visit(term.getExpr()));
		result.append(visit(term.getRightProcess()));
		result.append(")");
		return result.toString();
	}

	@Override
	public String visitTimeStartByProcess(TimeStartByProcess term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getExpr()));
		result.append(" <| ");
		result.append(visit(term.getCircusProcess()));
		result.append(")");
		return result.toString();
	}

	@Override
	public String visitTimedInterruptProcess(TimedInterruptProcess term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getLeftProcess()));
		result.append(" /^\\ ");
		result.append(visit(term.getExpr()));
		result.append(visit(term.getRightProcess()));
		result.append(")");
		return result.toString();
	}
	
	@Override
	public String visitTimeEndByProcess(TimeEndByProcess term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getCircusProcess()));
		result.append(" |> ");
		result.append(visit(term.getExpr()));
		result.append(")");
		return result.toString();
	}
	
	@Override
	public String visitTimedInterruptAction(TimedInterruptAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getLeftAction()));
		result.append(" /^\\ ");
		result.append(visit(term.getExpr()));
		result.append(visit(term.getRightAction()));
		result.append(")");
		return result.toString();
	}
	
	@Override
	public String visitTimeStartByAction(TimeStartByAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getExpr()));
		result.append(" <| ");
		result.append(visit(term.getCircusAction()));
		result.append(")");
		return result.toString();
	}
	
	@Override
	public String visitTimeEndByAction(TimeEndByAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getCircusAction()));
		result.append(" |> ");
		result.append(visit(term.getExpr()));
		result.append(")");
		return result.toString();
	}

	@Override
	public String visitTimeoutAction(TimeoutAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getLeftAction()));
		result.append("[>");
		result.append(visit(term.getExpr()));
		result.append(visit(term.getRightAction()));
		result.append(")");
		return result.toString();
	}
	
	@Override
	public String visitWaitExprAction(WaitExprAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("( wait ");
		result.append(visit(term.getExpr()));
		result.append(" @ ");
		result.append(visit(term.getCircusAction()));
		result.append(")");
		return result.toString();
	}

	@Override
	public String visitWaitAction(WaitAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("( wait ");
		result.append(visit(term.getExpr()));
		result.append(")");
		return result.toString();
	}
	
	@Override
	public String visitPrefixingTimeAction(PrefixingTimeAction term) {
		StringBuilder result= new StringBuilder("");
		result.append("(");
		result.append(visit(term.getCommunication()));
		result.append(" @ ");
		result.append(term.getChannelElapsedTimeDeclName());
		result.append("->");
		result.append(visit(term.getExpr()));
		result.append(visit(term.getCircusAction()));
		result.append(")");
		return result.toString();
	}
}
