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

import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.AssignmentCommand;
import net.sourceforge.czt.circus.ast.AssignmentPairs;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusActionList;
import net.sourceforge.czt.circus.ast.CircusGuardedCommand;
import net.sourceforge.czt.circus.ast.DoGuardedCommand;
import net.sourceforge.czt.circus.ast.IfGuardedCommand;
import net.sourceforge.czt.circus.ast.SpecStmtCommand;
import net.sourceforge.czt.circus.ast.VarDeclCommand;
import net.sourceforge.czt.circus.visitor.AssignmentCommandVisitor;
import net.sourceforge.czt.circus.visitor.CircusActionListVisitor;
import net.sourceforge.czt.circus.visitor.DoGuardedCommandVisitor;
import net.sourceforge.czt.circus.visitor.IfGuardedCommandVisitor;
import net.sourceforge.czt.circus.visitor.SpecStmtCommandVisitor;
import net.sourceforge.czt.circus.visitor.VarDeclCommandVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZNameList;


/**
 *
 * @author Leo Freitas
 */
public class CommandChecker
  extends Checker<CircusCommunicationList>
  implements 
      SpecStmtCommandVisitor<CircusCommunicationList>,      // C.17.1, C.17.4, C.17.5
      AssignmentCommandVisitor<CircusCommunicationList>,    // C.17.2
      VarDeclCommandVisitor<CircusCommunicationList>,       // C.16.1, C.17.3
      IfGuardedCommandVisitor<CircusCommunicationList>,     // C.17.7, C.17.8, C.17.9, C.17.10
      DoGuardedCommandVisitor<CircusCommunicationList>,     // C.17.7-2
      CircusActionListVisitor<CircusCommunicationList>      // C.17.8, C.17.9, C.17.10
      
{  
  
  private CircusGuardedCommand currentGuardedCommand_;
    
  /** Creates a new instance of CommandChecker
   * @param typeChecker 
   */
  public CommandChecker(TypeChecker typeChecker)
  {
    super(typeChecker);    
    currentGuardedCommand_ = null;
  }
  
  protected List<NameTypePair> typeCheckZNameList(ZNameList list, Term term)
  {
    // check no duplicate names in the frame.
    checkForDuplicateNames(list, term);  
    
    List<NameTypePair> localVars = factory().list();
    
    // check the names in the frame are in local variable scope
    int i = 1;
    for(Name name : list)
    {     
      // only get type for local names
      Type type = getLocalType(name);
      if (isLocalVar(type))
      {        
        localVars.add(factory().createNameTypePair(name, type));
      }
      else
      {
        Object[] params = { 
          getCurrentProcessName(),
          getCurrentActionName(), 
          name, i, type, 
          getConcreteSyntaxSymbol(term) 
        };
        error(term, ErrorMessage.INVALID_NAMELIST_IN_COMMAND, params);                
      }
      i++;
    }
    return localVars;
  }
  
  /**
   * 
   * @param term
   * @return
   * @law C.17.1, C.17.4, C.17.5
   */
  public CircusCommunicationList visitSpecStmtCommand(SpecStmtCommand term)
  {
    // check within action scope
    checkActionParaScope(term, null);      
    
    // check for duplicate names and their local scope
    List<NameTypePair> localVars = typeCheckZNameList(term.getZFrame(), term);
    
    typeCheckPred(term, term.getPre());
    typeCheckPred(term, term.getPost());
    
    CircusCommunicationList result = factory().createEmptyCircusCommunicationList();
    actionChecker().getCurrentActionSignature().getLocalVars().getNameTypePair().addAll(localVars);
    
    warningManager().warn("Specification statement command still requires StateUpdate in process signature." +
      "\n\tProcess...: {0}\n\tAction....: {1}", getCurrentProcessName(), getCurrentActionName());    
  
    return result;
  }
  
  /**
   * 
   * @param term
   * @return
   * @law C.17.2
   */
  public CircusCommunicationList visitAssignmentCommand(AssignmentCommand term)
  {
    // check within action scope
    checkActionParaScope(term, null);      
    
    AssignmentPairs apairs = term.getAssignmentPairs();
    ZNameList lhs = apairs.getZLHS();
    ZExprList rhs = apairs.getZRHS();
    
    // check for duplicate names and their local scope    
    List<NameTypePair> localVars = typeCheckZNameList(lhs, term);
    
    // their sizes is enforced by the parser, by double check here
    // for the case of manually created assignments
    if (lhs.size() != rhs.size())
    {
      Object[] params = {
        getCurrentProcessName(),
        getCurrentActionName(),
        lhs.size(), rhs.size()
      };
      error(term, ErrorMessage.UNBALANCED_ASSIGNMENT_PAIRS, params);
    }
    else 
    {
      int i = 1;      
      Iterator<Expr> itExpr = rhs.iterator();      
      for(NameTypePair ntp : localVars)
      {
        // get the values
        assert itExpr.hasNext();        
        
        Expr expr  = itExpr.next();        
        Type2 expected = GlobalDefs.unwrapType(ntp.getType());
        Type2 found    = expr.accept(exprChecker());
                
        if (!unify(found, expected).equals(UResult.SUCC)) 
        {
          Object [] params = { 
            getCurrentProcessName(), 
            getCurrentActionName(), 
            ntp.getName(), i, expected, found };
          error(term, ErrorMessage.ASSIGNMENT_COMMAND_DONT_UNIFY, params);          
        }
        i++;        
      }
    }
    
    CircusCommunicationList result = factory().createEmptyCircusCommunicationList();
    actionChecker().getCurrentActionSignature().getLocalVars().getNameTypePair().addAll(localVars);
    
    warningManager().warn("Assignment command still requires StateUpdate in process signature." +
      "\n\tProcess...: {0}\n\tAction....: {1}", getCurrentProcessName(), getCurrentActionName());    
        
    return result; 
  }
  
  /**
   * Typechecks variable declaration commands, as well as qualified commands.
   * @param term
   * @return
   * @law C.16.1, C.17.3
   */
  public CircusCommunicationList visitVarDeclCommand(VarDeclCommand term)
  {
    checkActionParaScope(term, null);
    
    // variable declaration commands do not allow qualified declarations    
    // and types of declarations do not need to be finite
    List<NameTypePair> gParams = typeCheckCircusDeclList(
      term, term.getZDeclList(), false /* considerFiniteness */,
      false /* allowQualifiedDecl */,  ErrorMessage.INVALID_DECL_IN_VARDECLCOMMAND, 
      factory().<Object>list(getCurrentProcessName(), getCurrentActionName()));
  
    // put the declared parameters into the action's scope
    typeEnv().enterScope();
    
    // add variables to the state - and current scope only.
    List<NameTypePair> allVars = addStateVars(gParams);    
    
    // check the inner action now with the parameters in scope
    CircusCommunicationList commList = visit(term.getCircusAction());
    
    // updates the local variable signature for variable decl command - duplicates are fine (?) TODO:CHECK
    actionChecker().getCurrentActionSignature().getLocalVars().getNameTypePair().addAll(allVars);
        
    typeEnv().exitScope();    
    
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.17.7
   */
  public CircusCommunicationList visitIfGuardedCommand(IfGuardedCommand term)
  {
    currentGuardedCommand_ = term;
    
    // type check all guards - note here we allow room for guard jokers ;-)
    // but the type checker only captures normal guards - via CircusActionList
    CircusCommunicationList commList = term.getGuardedActionList().accept(commandChecker());
    
    currentGuardedCommand_ = null ;    
    return commList;
  }
  
  /**
   * 
   * @param term
   * @return
   * @law C.17.7-2
   */
  public CircusCommunicationList visitDoGuardedCommand(DoGuardedCommand term)
  {    
    currentGuardedCommand_ = term;
    
    // type check all guards - note here we allow room for guard jokers ;-)
    // but the type checker only captures normal guards - via CircusActionList
    CircusCommunicationList commList = term.getActionList().accept(commandChecker());
    
    currentGuardedCommand_ = null;
        
    return commList;
  }
  
  public CircusCommunicationList visitCircusActionList(CircusActionList term)
  {
    assert currentGuardedCommand_ != null : "Cannot check guards of null guarded command";
    
    // check scope
    checkActionParaScope(term, null);
     
    CircusCommunicationList commList = factory().createEmptyCircusCommunicationList();
    
    // if there are no guards, raise a warning.
    if (term.isEmpty())
    {
      Object[] params = {
        getCurrentProcessName(),
        getCurrentActionName(),
        getConcreteSyntaxSymbol(currentGuardedCommand_)
      };
      warningManager().warn(term, WarningMessage.EMPTY_GUARDED_COMMAND, params);      
    }
    else
    {
      Iterator<CircusAction> it = term.iterator();
      CircusAction action = it.next();
      commList = visit(action);
      // type check each guarded action joining their signatures    
      while (it.hasNext())
      {
        CircusAction next = it.next();
        CircusCommunicationList nextCommList = visit(next);
        GlobalDefs.addAllNoDuplicates(nextCommList, commList);
      }
    }     
    return commList;
  }    
}
