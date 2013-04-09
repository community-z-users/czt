package net.sourceforge.czt.typecheck.circustime;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circustime.ast.PrefixingTimeAction;
import net.sourceforge.czt.circustime.ast.TimeEndByAction;
import net.sourceforge.czt.circustime.ast.TimeStartByAction;
import net.sourceforge.czt.circustime.ast.TimedinterruptAction;
import net.sourceforge.czt.circustime.ast.TimeoutAction;
import net.sourceforge.czt.circustime.ast.WaitAction;
import net.sourceforge.czt.circustime.ast.WaitExprAction;
import net.sourceforge.czt.circustime.visitor.PrefixingTimeActionVisitor;
import net.sourceforge.czt.circustime.visitor.TimeEndByActionVisitor;
import net.sourceforge.czt.circustime.visitor.TimeStartByActionVisitor;
import net.sourceforge.czt.circustime.visitor.TimedinterruptActionVisitor;
import net.sourceforge.czt.circustime.visitor.TimeoutActionVisitor;
import net.sourceforge.czt.circustime.visitor.WaitActionVisitor;
import net.sourceforge.czt.circustime.visitor.WaitExprActionVisitor;
import net.sourceforge.czt.typecheck.circus.ErrorAnn;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.circustime.ErrorMessage;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.util.ZString;

public class ActionChecker
  extends net.sourceforge.czt.typecheck.circus.ActionChecker
  implements
  TimeoutActionVisitor<CircusCommunicationList>,
  TimeStartByActionVisitor<CircusCommunicationList>,
  TimeEndByActionVisitor<CircusCommunicationList>,
  TimedinterruptActionVisitor<CircusCommunicationList>,
  WaitActionVisitor<CircusCommunicationList>,
  WaitExprActionVisitor<CircusCommunicationList>,
  PrefixingTimeActionVisitor<CircusCommunicationList>
  
// Add Action Visitor for each circus time action
{	
  private final Expr arithmos_; 
  protected net.sourceforge.czt.typecheck.circus.ActionChecker circusActionChecker_;
  
  /** Creates a new instance of ActionChecker */
  public ActionChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    circusActionChecker_ = new net.sourceforge.czt.typecheck.circus.ActionChecker(typeChecker); 
    arithmos_ = factory().createRefExpr(factory().createZDeclName(ZString.ARITHMOS));
  }
  
  
  
  public CircusCommunicationList visitPrefixingTimeAction(PrefixingTimeAction term) {
	    //This section is similar to the visitPrefixingAction for communication channel type-checking
	  	checkActionParaScope(term, null);
		// enter the scope for input fields
	    typeEnv().enterScope();
	    Communication comm = term.getCommunication();
	    List<NameTypePair> comSig = comm.accept(commChecker());
	    CircusCommunicationList commList = visit(term.getCircusAction());	    
	    if (term.isAtPrefixingAction()){
	    	// Typechecking for the channel elapsed time (N) (c@N -> A)
	    	// retrieve the type of this name.
	    	Name varName = term.getChannelElapsedTime();
	    	//expected type of this new variable
	    	Type2 expected = arithmos_.accept(exprChecker());
	    	// The type of channel elapsed time will be arithmetic 
	    	Type2 newType = ((PowerType)expected).getType();
	    	NameTypePair pair = factory().createNameTypePair(varName , newType);
	    	typeEnv().add(pair);			
	    }
	    if(term.isPrefixingExprAction()){
	    	typeCheckTimeExpr(term, term.getExpr());
	    }
	    if (term.isAtPrefixingExprAction()){
	    	// Typechecking for the channel elapsed time (N) (c@N -> A)
	    	// retrieve the type of this name.
	    	Name varName = term.getChannelElapsedTime();	    	
	    	//expected type of this new variable
	    	Type2 expected = arithmos_.accept(exprChecker());
	    	// The type of channel elapsed time will be arithmetic 
	    	Type2 newType = ((PowerType)expected).getType();
	    	NameTypePair pair = factory().createNameTypePair(varName , newType);
	    	typeEnv().add(pair);
	    	typeCheckTimeExpr(term, term.getExpr());	    	
	    }
	    // close input variables scope after analysing the circus time action
	    typeEnv().exitScope();	
	return commList;
}

	@Override
	public CircusCommunicationList visitWaitExprAction(WaitExprAction term) {
		checkActionParaScope(term, null);
		//enter in scope
		typeEnv().enterScope();
		//add the wait expression in the scope 
		//retrieve expression and type
		Expr expr = term.getExpr();
	    Type2 exprType = expr.accept(exprChecker());
	    NameTypePair pair = factory().createNameTypePair(term.getName() , exprType);
    	typeEnv().add(pair);
		CircusCommunicationList commList = visit(term.getCircusAction());
		typeCheckWaitTimeExpr(term, term.getExpr());
		typeEnv().exitScope();
		return commList;
	}

	@Override
	public CircusCommunicationList visitWaitAction(WaitAction term) {
		checkActionParaScope(term, null);
		CircusCommunicationList commList = visitBasicAction(term);
		typeCheckWaitTimeExpr(term, term.getExpr());
		return commList;
	} 


	@Override
	public CircusCommunicationList visitTimedinterruptAction(
			TimedinterruptAction term) {
		checkActionParaScope(term, null);
		CircusCommunicationList commListL = visit(term.getLeftAction());
		CircusCommunicationList commListR = visit(term.getRightAction());
		typeCheckTimeExpr(term, term.getExpr());
		CircusCommunicationList result = factory().createCircusCommunicationList(commListR);
	    GlobalDefs.addAllNoDuplicates(0, commListL, result);    
	    return result;
	}

	@Override
	public CircusCommunicationList visitTimeEndByAction(TimeEndByAction term) {
		checkActionParaScope(term, null);
		CircusCommunicationList commList = visit(term.getCircusAction());
		typeCheckTimeExpr(term, term.getExpr());    
	    return commList;
	}

	@Override
	public CircusCommunicationList visitTimeStartByAction(TimeStartByAction term) {
		checkActionParaScope(term, null);
		CircusCommunicationList commList = visit(term.getCircusAction());
		typeCheckTimeExpr(term, term.getExpr());    
	    return commList;
	}

	@Override
	public CircusCommunicationList visitTimeoutAction(TimeoutAction term) {
		checkActionParaScope(term, null);
		CircusCommunicationList commListL = visit(term.getLeftAction());
		CircusCommunicationList commListR = visit(term.getRightAction());
		typeCheckTimeExpr(term, term.getExpr());
		CircusCommunicationList result = factory().createCircusCommunicationList(commListR);
	    GlobalDefs.addAllNoDuplicates(0, commListL, result);    
	    return result;	
	}
	
	protected void typeCheckTimeExpr(Term term, Expr expr)
	  {
		Type2 found = GlobalDefs.unwrapType(expr.accept(exprChecker()));
		Type2 expected = arithmos_.accept(exprChecker());
			if (expected instanceof PowerType){
					expected = ((PowerType)expected).getType();
			}
			if (!unify(found, expected).equals(UResult.SUCC)){
				Object[] params = {
						getCurrentProcessName(), getCurrentActionName(),
						term.getClass().getSimpleName(), expr, expected, found
				};
				ErrorAnn errorAnn = errorAnn(term, ErrorMessage.CIRCUS_TIME_EXPR_DONT_UNIFY, params);
			    error(term, errorAnn);
			}
	    
	  }
	  
	  protected void typeCheckWaitTimeExpr(Term term, Expr expr)
	  {
		  	  
		  Type2 expected_arith = null, expected_power = null;  
		  Type2 found = GlobalDefs.unwrapType(expr.accept(exprChecker()));
		  Type2 expected = arithmos_.accept(exprChecker());
		  if (expected instanceof PowerType){
			expected_arith = ((PowerType)expected).getType();
			expected_power = ((PowerType)expected);
		  }	
		    
		  if (!unify(found, expected_arith).equals(UResult.SUCC) && !unify(found, expected_power).equals(UResult.SUCC)){
	      Object[] params = {
	        getCurrentProcessName(), getCurrentActionName(),
	        term.getClass().getSimpleName(), expr, expected, found
	      	};
	      ErrorAnn errorAnn = errorAnn(term, ErrorMessage.CIRCUS_TIME_EXPR_DONT_UNIFY, params);
	      error(term, errorAnn);
		  }
	    
	  }	 
	  
	  private ErrorAnn errorAnn(Term term, ErrorMessage error,
				Object[] params) {
			ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
				    sectName(), GlobalDefs.nearestLocAnn(term), markup());
				  return errorAnn;
		}
}
