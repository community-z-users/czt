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
import net.sourceforge.czt.circus.ast.AlphabetisedParallelProcess;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.HideProcess;
import net.sourceforge.czt.circus.ast.IndexedProcess;
import net.sourceforge.czt.circus.ast.ParallelProcess;
import net.sourceforge.czt.circus.ast.ParamProcess;
import net.sourceforge.czt.circus.ast.ProcessIdx;
import net.sourceforge.czt.circus.ast.ProcessIte;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.RenameProcess;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelProcessVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.CallProcessVisitor;
import net.sourceforge.czt.circus.visitor.HideProcessVisitor;
import net.sourceforge.czt.circus.visitor.IndexedProcessVisitor;
import net.sourceforge.czt.circus.visitor.ParallelProcessVisitor;
import net.sourceforge.czt.circus.visitor.ParamProcessVisitor;
import net.sourceforge.czt.circus.visitor.Process1Visitor;
import net.sourceforge.czt.circus.visitor.Process2Visitor;
import net.sourceforge.czt.circus.visitor.ProcessIdxVisitor;
import net.sourceforge.czt.circus.visitor.ProcessIteVisitor;
import net.sourceforge.czt.circus.visitor.RenameProcessVisitor;
import net.sourceforge.czt.circustime.ast.ProcessTime1;
import net.sourceforge.czt.circustime.ast.ProcessTime2;
import net.sourceforge.czt.circustime.visitor.ProcessTime1Visitor;
import net.sourceforge.czt.circustime.visitor.ProcessTime2Visitor;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;

public class ProcessChecker extends
		Checker<CircusCommunicationList> implements
		ProcessTime2Visitor<CircusCommunicationList>,
		ProcessTime1Visitor<CircusCommunicationList>,
		BasicProcessVisitor<CircusCommunicationList>,
		ParamProcessVisitor<CircusCommunicationList>,      // C.6.3, C.6.6
	    IndexedProcessVisitor<CircusCommunicationList>,    // C.6.4, C.6.7
	    ZParaListVisitor<CircusCommunicationList>,         // C.7.1, C.7.2      
	    CallProcessVisitor<CircusCommunicationList>,       // C.8.2, C.8.9--C.8.15
	    HideProcessVisitor<CircusCommunicationList>,       // C.8.3
	    ParallelProcessVisitor<CircusCommunicationList>,   // C.8.8
	    AlphabetisedParallelProcessVisitor<CircusCommunicationList>, //  C.8.8-2
	    RenameProcessVisitor<CircusCommunicationList>,     // C.8.16
	    ProcessIteVisitor<CircusCommunicationList>,        // C.8.17--C.8.21-2
	    ProcessIdxVisitor<CircusCommunicationList>     
		{
	
	
    //a Circus process checker
	protected net.sourceforge.czt.typecheck.circus.ProcessChecker circusProcessChecker_;


	public ProcessChecker(TypeChecker typeChecker) 
	{
		super(typeChecker);
		circusProcessChecker_ = new net.sourceforge.czt.typecheck.circus.ProcessChecker(typeChecker);
	}
	
	
	protected CircusCommunicationList typeCheckProcessTimeExpr(CircusProcess term, Expr expr) 
	{
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
	
  @Override
  public ProcessSignature setCurrentProcessSignature(ProcessSignature sig)
  {
	 return circusProcessChecker_.setCurrentProcessSignature(sig);
  }
  
  @Override
  public ProcessSignature getCurrentProcessSignature()
  {
	 return circusProcessChecker_.getCurrentProcessSignature();
  }
  
  @Override
  public void checkProcessSignature(Object term)
  {
	  circusProcessChecker_.checkProcessSignature(term);
  }


@Override
public CircusCommunicationList visitBasicProcess(BasicProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitProcessIdx(ProcessIdx term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitProcessIte(ProcessIte term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitRenameProcess(RenameProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitAlphabetisedParallelProcess(
		AlphabetisedParallelProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitParallelProcess(ParallelProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitHideProcess(HideProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitCallProcess(CallProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitZParaList(ZParaList term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitIndexedProcess(IndexedProcess term) {
	return term.accept(circusProcessChecker_);
}


@Override
public CircusCommunicationList visitParamProcess(ParamProcess term) {
	return term.accept(circusProcessChecker_);
}

  
}
