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
package net.sourceforge.czt.circusconf.util;

import net.sourceforge.czt.circusconf.ast.ConfidentialityAction;
import net.sourceforge.czt.circusconf.ast.ConfidentialityProcess;
import net.sourceforge.czt.circusconf.visitor.CircusConfVisitor;

/**
 * @author Leo Freitas
 */
public class PrintVisitor
  extends net.sourceforge.czt.circus.util.PrintVisitor
 // implements any element you want to have toString capability for CircusTime
  implements CircusConfVisitor<String>
{

	@Override
	public String visitConfidentialityAction(ConfidentialityAction term) {
	    return "<" + term.getCircusAction().accept(this) + ">";
	}

	@Override
	public String visitConfidentialityProcess(ConfidentialityProcess term) {
	    return "<" + term.getCircusProcess().accept(this) + ">";
	}
}
