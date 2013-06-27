/*
  Copyright (C) 2004, 2005, 2006 Petra Malik, Leo Freitas
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

package net.sourceforge.czt.print.circustime;

import java.util.Properties;

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
import net.sourceforge.czt.parser.circus.CircusKeyword;
import net.sourceforge.czt.parser.circustime.CircusTimeKeyword;
import net.sourceforge.czt.parser.circustime.CircusTimeToken;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.ParenAnn;
import net.sourceforge.czt.z.util.WarningManager;

/**
 * An Circus visitor used for printing.
 * 
 * @author Petra Malik, Leo Freitas
 */
public class CircusTimePrintVisitor extends
		net.sourceforge.czt.print.circus.CircusPrintVisitor implements
		CircusTimeVisitor<Object> {

	public CircusTimePrintVisitor(SectionInfo si, ZPrinter printer,
			WarningManager wm) {
		super(si, printer, wm);
	}

	public CircusTimePrintVisitor(SectionInfo si, ZPrinter printer,
			Properties properties, WarningManager wm) {
		super(si, printer, properties, wm);
	}

	/* Support for Circus Time : Process */

	// TODO: AstToPrintTreeVisitor needs to add the ParenAnn to the places where
	// precendences are to observed, such that x+y*z doesn't get to be x+(y*z).
	//
	// Note these rules for Circus also need adjusting. Follow what's done in Z.

	public Object visitTimeEndByProcess(TimeEndByProcess term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getCircusProcess());
		print(CircusTimeKeyword.CIRCENDBY);
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitTimeStartByProcess(TimeStartByProcess term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		print(CircusTimeKeyword.CIRCSTARTBY);
		visit(term.getCircusProcess());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitTimeoutProcess(TimeoutProcess term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getLeftProcess());
		print(CircusTimeKeyword.CIRCTIMEOUT);
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		visit(term.getRightProcess());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitTimedInterruptProcess(TimedInterruptProcess term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getLeftProcess());
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		visit(term.getRightProcess());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	/* Support for Circus Time : Action */

	public Object visitTimeEndByAction(TimeEndByAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getCircusAction());
		print(CircusTimeKeyword.CIRCENDBY);
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitTimeStartByAction(TimeStartByAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		print(CircusTimeKeyword.CIRCSTARTBY);
		visit(term.getCircusAction());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitTimeoutAction(TimeoutAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getLeftAction());
		print(CircusTimeKeyword.CIRCTIMEOUT);
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		visit(term.getRightAction());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitTimedInterruptAction(TimedInterruptAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getLeftAction());
		print(CircusTimeToken.LCIRCTIME);
		visit(term.getExpr());
		print(CircusTimeToken.RCIRCTIME);
		visit(term.getRightAction());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitWaitAction(WaitAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		print(CircusTimeKeyword.CIRCWAIT);
		visit(term.getExpr());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitWaitExprAction(WaitExprAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		print(CircusTimeKeyword.CIRCWAIT);
		visit(term.getName());
		print(ZKeyword.COLON);
		visit(term.getExpr());
		print(CircusKeyword.CIRCSPOT);
		visit(term.getCircusAction());
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

	public Object visitPrefixingTimeAction(PrefixingTimeAction term) {
		final boolean braces = term.getAnn(ParenAnn.class) != null;
		if (braces)
			print(ZToken.LPAREN);
		visit(term.getCommunication());
		if (term.isAtPrefixingAction()) {
			print(CircusTimeKeyword.ATTIME);
			print(CircusKeyword.PREFIXTHEN);
			visit(term.getCircusAction());
		} else if (term.isPrefixingExprAction()) {
			print(CircusKeyword.PREFIXTHEN);
			print(CircusTimeToken.LCIRCTIME);
			visit(term.getExpr());
			print(CircusTimeToken.RCIRCTIME);
			visit(term.getCircusAction());
		} else if (term.isAtPrefixingExprAction()) {
			print(CircusTimeKeyword.ATTIME);
			print(CircusKeyword.PREFIXTHEN);
			print(CircusTimeToken.LCIRCTIME);
			visit(term.getExpr());
			print(CircusTimeToken.RCIRCTIME);
			visit(term.getCircusAction());
		}
		if (braces)
			print(ZToken.RPAREN);
		return null;
	}

}
