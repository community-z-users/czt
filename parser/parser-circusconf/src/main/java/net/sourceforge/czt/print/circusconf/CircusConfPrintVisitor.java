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

package net.sourceforge.czt.print.circusconf;

import java.util.Properties;

import net.sourceforge.czt.circusconf.ast.ConfidentialityAction;
import net.sourceforge.czt.circusconf.ast.ConfidentialityProcess;
import net.sourceforge.czt.circusconf.visitor.CircusConfVisitor;
import net.sourceforge.czt.parser.circusconf.CircusConfToken;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.util.WarningManager;
//import net.sourceforge.czt.parser.circusconf.CircusConfToken;

/**
 * An Circus visitor used for printing.
 *
 * @author Petra Malik, Leo Freitas
 */
public class CircusConfPrintVisitor
    extends net.sourceforge.czt.print.circus.CircusPrintVisitor
    implements CircusConfVisitor<Object> {
    
    /**
     * Creates a new Object-Z print visitor.
     * The section information should be able to provide information of
     * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
     */
    public CircusConfPrintVisitor(SectionInfo si, ZPrinter printer, WarningManager wm) {
        super(si, printer, wm);
    }
    
    public CircusConfPrintVisitor(SectionInfo si, ZPrinter printer, Properties properties, WarningManager wm) {
        super(si, printer, properties, wm);
    }
    
    /***********************************************************
     * Auxiliary methods
     ***********************************************************/
 
    @Override
    public Object visitConfidentialityProcess(ConfidentialityProcess term)
    {	
    	print(CircusConfToken.LCIRCCONF);
    	visit(term.getCircusProcess());
    	print(CircusConfToken.RCIRCCONF);
    	return null;
    }
    
    @Override
    public Object visitConfidentialityAction(ConfidentialityAction term)
    {	
    	print(CircusConfToken.LCIRCCONF);
    	visit(term.getCircusAction());
    	print(CircusConfToken.RCIRCCONF);
    	return null;
    }
}
