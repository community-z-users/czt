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
package net.sourceforge.czt.typecheck.circus;

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.CallProcessVisitor;
import net.sourceforge.czt.typecheck.circus.ErrorAnn;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;

/**
 * <p>
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined.
 * </p>
 * <p>
 * In Circus, due to the presence of mutually recurisve calls,
 * we also have post checking for action and process calls. 
 * </p>
 */
public class PostChecker
  extends Checker<net.sourceforge.czt.typecheck.z.ErrorAnn>
implements 
  CallProcessVisitor<net.sourceforge.czt.typecheck.z.ErrorAnn>,
  CallActionVisitor<net.sourceforge.czt.typecheck.z.ErrorAnn>
{

  protected net.sourceforge.czt.typecheck.z.PostChecker zPostChecker_;

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPostChecker_ =
      new net.sourceforge.czt.typecheck.z.PostChecker(typeChecker);
  }

  public net.sourceforge.czt.typecheck.z.ErrorAnn visitTerm(Term term)
  {
    return term.accept(zPostChecker_);
  }
  
  @Override
  public net.sourceforge.czt.typecheck.z.ErrorAnn visitCallAction(CallAction term)
  {    
    // MuActions are not within action para scope :-(
    assert isWithinProcessParaScope() : "Action call post checking requires process scope";
    
    boolean added;
    net.sourceforge.czt.typecheck.z.ErrorAnn result;
    ZName zName = term.getZName();
    UndeclaredAnn uAnn = zName.getAnn(UndeclaredAnn.class);
    final boolean nameIsUndeclared = uAnn != null;
    if (nameIsUndeclared) 
    {            
      result = createUndeclaredNameError(zName);
      GlobalDefs.removeAnn(zName, uAnn);      
      added = addErrorAnn(term, result);
    }
    else
    {
      // check calls agains
      Type2 type = getType2FromAnns(term); 
      if (type instanceof UnknownType) 
      {
        type = GlobalDefs.unwrapType(getLocalType(zName));
      }
      List<ErrorAnn> callErrors = checkCallActionConsistency(type, term);      
      
      // add the errors to all terms.
      added = false;
      result = null;
      for(ErrorAnn e : callErrors)
      {
        boolean r = addErrorAnn(term, e);
        added = added || r;
      }
      
      // accumulate all post check errors at once.
      if (added)
      {        
        Object[] params = { getCurrentProcessName(), getConcreteSyntaxSymbol(term), term, callErrors.size() };
        result = errorAnn(term, ErrorMessage.POSTCHECKING_CALL_ERROR, params);
        // cast it as a Circus ErrorAnn
        ((ErrorAnn)result).addCallErrors(callErrors);
      }
    }      
    return added ? result : null;
  }
  
  @Override
  public net.sourceforge.czt.typecheck.z.ErrorAnn visitCallProcess(CallProcess term)
  { 
    boolean added;
    net.sourceforge.czt.typecheck.z.ErrorAnn result;
    ZName zName = term.getCallExpr().getZName();
    UndeclaredAnn uAnn = zName.getAnn(UndeclaredAnn.class);
    final boolean nameIsUndeclared = uAnn != null;
    if (nameIsUndeclared) 
    {            
      result = createUndeclaredNameError(zName);
      GlobalDefs.removeAnn(zName, uAnn);      
      added = addErrorAnn(term, result);
    }
    else
    {
      Type type = getGlobalType(zName);
      List<ErrorAnn> callErrors = checkCallProcessConsistency(
        GlobalDefs.unwrapType(type), term, false /* checkProcessScope */);      
      
      // add the errors to all terms.
      added = false;
      result = null;
      for(ErrorAnn e : callErrors)
      {
        boolean r = addErrorAnn(term, e);
        added = added || r;
      }
      
      // accumulate all post check errors at once.
      if (added)
      {        
        Object[] params = { getCurrentProcessName(), getConcreteSyntaxSymbol(term), term, callErrors.size() };
        result = errorAnn(term, ErrorMessage.POSTCHECKING_CALL_ERROR, params);
        // cast it as a Circus ErrorAnn
        ((ErrorAnn)result).addCallErrors(callErrors);
      }
    }      
    return added ? result : null;
  }
}
