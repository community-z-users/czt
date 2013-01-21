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
import net.sourceforge.czt.circustime.ast.TimedinterruptAction;
import net.sourceforge.czt.circustime.ast.TimedinterruptProcess;
import net.sourceforge.czt.circustime.ast.TimeoutAction;
import net.sourceforge.czt.circustime.ast.TimeoutProcess;
import net.sourceforge.czt.circustime.ast.WaitAction;
import net.sourceforge.czt.circustime.ast.WaitExprAction;
import net.sourceforge.czt.circustime.visitor.CircusTimeVisitor;

/**
 * @author Leo Freitas
 */
public class PrintVisitor
  extends net.sourceforge.czt.z.util.PrintVisitor
 // implements any element you want to have toString capability for CircusTime
  implements CircusTimeVisitor<String>
{

	@Override
	public String visitTimedinterruptProcess(TimedinterruptProcess term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitTimeEndByAction(TimeEndByAction term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitTimeoutProcess(TimeoutProcess term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitTimeoutAction(TimeoutAction term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitTimeStartByProcess(TimeStartByProcess term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitTimedinterruptAction(TimedinterruptAction term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitPrefixingTimeAction(PrefixingTimeAction term) {
		StringBuilder result = new StringBuilder();
		return result.toString();
		// TODO: drill into the definition of the class strucuture and return a sensible debugging string for you...
	}

	@Override
	public String visitTimeStartByAction(TimeStartByAction term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitTimeEndByProcess(TimeEndByProcess term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visitWaitExprAction(WaitExprAction term) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public String visitWaitAction(WaitAction term) {
		// TODO Auto-generated method stub
		return null;
	}

}
