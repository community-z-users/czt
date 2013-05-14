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

package net.sourceforge.czt.print.ohcircus;

import java.util.Iterator;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.CircusVisitor;
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
import net.sourceforge.czt.ohcircus.ast.CallMethod;
import net.sourceforge.czt.ohcircus.ast.DoOhCircusGuardedCommand;
import net.sourceforge.czt.ohcircus.ast.GuardedMethod;
import net.sourceforge.czt.ohcircus.ast.IfOhCircusGuardedCommand;
import net.sourceforge.czt.ohcircus.ast.LetMuMethod;
import net.sourceforge.czt.ohcircus.ast.LetVarMethod;
import net.sourceforge.czt.ohcircus.ast.MuMethod;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassDef;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassInitialState;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassPara;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassRef;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassRefList;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassRefType;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassSignature;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassSignatureList;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassState;
import net.sourceforge.czt.ohcircus.ast.OhCircusClassType;
import net.sourceforge.czt.ohcircus.ast.OhCircusDot;
import net.sourceforge.czt.ohcircus.ast.OhCircusGuardedCommand;
import net.sourceforge.czt.ohcircus.ast.OhCircusMethodList;
import net.sourceforge.czt.ohcircus.ast.OhCircusMethodPara;
import net.sourceforge.czt.ohcircus.ast.OhCircusMethodSignature;
import net.sourceforge.czt.ohcircus.ast.OhCircusMethodSignatureList;
import net.sourceforge.czt.ohcircus.ast.OhCircusMethodType;
import net.sourceforge.czt.ohcircus.ast.OhExprList;
import net.sourceforge.czt.ohcircus.ast.ParamMethod;
import net.sourceforge.czt.ohcircus.ast.PredExpr;
import net.sourceforge.czt.ohcircus.ast.QualifiedClassDecl;
import net.sourceforge.czt.ohcircus.ast.SchExprMethod;
import net.sourceforge.czt.ohcircus.ast.SeqMethod;
import net.sourceforge.czt.ohcircus.ast.VarDeclOhCircusCommand;
import net.sourceforge.czt.ohcircus.visitor.OhCircusVisitor;
import net.sourceforge.czt.parser.circus.CircusKeyword;
import net.sourceforge.czt.parser.circus.CircusToken;
import net.sourceforge.czt.parser.circustime.CircusTimeKeyword;
import net.sourceforge.czt.parser.circustime.CircusTimeToken;
import net.sourceforge.czt.parser.ohcircus.OhCircusKeyword;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.util.ZUtils;
//import net.sourceforge.czt.parser.circustime.CircusTimeToken;

/**
 * An Circus visitor used for printing.
 *
 * @author Petra Malik, Leo Freitas
 */
public class OhCircusPrintVisitor
    extends net.sourceforge.czt.print.circus.CircusPrintVisitor
    implements OhCircusVisitor<Object> {
    
    public OhCircusPrintVisitor(SectionInfo si, ZPrinter printer, WarningManager wm) {
        super(si, printer, wm);        
    }
    
    public OhCircusPrintVisitor(SectionInfo si, ZPrinter printer, Properties properties, WarningManager wm) {
        super(si, printer, properties, wm);
    }
    
    /* Support for OhCircus Class and Methods */

    public Object visitOhCircusClassPara(OhCircusClassPara term) {
        printLPAREN(term);
        print(OhCircusKeyword.OHCIRCCLASS);
        visit(term.getName());
        print(CircusKeyword.CIRCDEF);
        //may be add some condition to detect extended class 
        print(OhCircusKeyword.OHCIRCEXTENDS); 
        visit(term.getName());
        visit(term.getOhCircusClassDef());
        print(CircusKeyword.CIRCSPOT);    
        printRPAREN(term);
        return null;
    }

    public Object visitOhCircusClassDef(OhCircusClassDef term) {
        printLPAREN(term);
        print(CircusKeyword.CIRCBEGIN);
        visit(term.getOhCircusClass());
        visit(term.getOhCircusClassInitialState());
        visit(term.getOhCircusClassState());
        print(CircusKeyword.CIRCEND);
        printRPAREN(term);
        return null;
    }


        public  Object visitOhCircusClassInitialState(OhCircusClassInitialState term) {
        	printLPAREN(term);
        	visit(term.getPred());
        	printRPAREN(term);
            return null;
        }
    
	@Override
	public Object visitOhCircusMethodSignatureList(
			OhCircusMethodSignatureList term) {
		// TODO Auto-generated method stub
		return null;
	}

	

	@Override
	public Object visitOhCircusClassRefList(OhCircusClassRefList term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitMuMethod(MuMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitVarDeclOhCircusCommand(VarDeclOhCircusCommand term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitCallMethod(CallMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitQualifiedClassDecl(QualifiedClassDecl term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusGuardedCommand(OhCircusGuardedCommand term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusDot(OhCircusDot term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitLetMuMethod(LetMuMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitDoOhCircusGuardedCommand(DoOhCircusGuardedCommand term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitParamMethod(ParamMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusClassState(OhCircusClassState term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitGuardedMethod(GuardedMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusClassType(OhCircusClassType term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusMethodList(OhCircusMethodList term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusClassSignature(OhCircusClassSignature term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitIfOhCircusGuardedCommand(IfOhCircusGuardedCommand term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusMethodSignature(OhCircusMethodSignature term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitPredExpr(PredExpr term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusMethodType(OhCircusMethodType term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusMethodPara(OhCircusMethodPara term) {
		// TODO Auto-generated method stub
		return null;
	}

	
	@Override
	public Object visitLetVarMethod(LetVarMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhExprList(OhExprList term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSchExprMethod(SchExprMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusClassSignatureList(
			OhCircusClassSignatureList term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSeqMethod(SeqMethod term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusClassRefType(OhCircusClassRefType term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitOhCircusClassRef(OhCircusClassRef term) {
		// TODO Auto-generated method stub
		return null;
	}    
      
 

  

}
