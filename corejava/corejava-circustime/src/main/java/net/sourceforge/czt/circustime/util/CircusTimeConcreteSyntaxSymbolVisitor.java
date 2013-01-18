/*
 * CircusTimeConcreteSyntaxSymbolVisitor.java
 *
 * Created on 08 June 2006, 15:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.circustime.util;


import net.sourceforge.czt.circustime.ast.*;
import net.sourceforge.czt.circustime.visitor.*;

import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.util.IsEmptyNameList;
import net.sourceforge.czt.z.util.StandardZ;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link CircusConcreteSyntaxSymbol}.  This can be used by the JEdit and
 * Eclipse plugins to produce an outline view (or structure tree) of
 * the source.
 *
 * @author leo
 */
public class CircusTimeConcreteSyntaxSymbolVisitor
  implements CircusTimeVisitor<CircusTimeConcreteSyntaxSymbol>
{

  private Utils utils_;

  public CircusTimeConcreteSyntaxSymbolVisitor()
  {
    utils_ = new UtilsImpl();
  }

  public CircusTimeConcreteSyntaxSymbolVisitor(Utils utils)
  {
    utils_ = utils;
  }


/* Support for Circus Time : Process */
  
 public CircusTimeConcreteSyntaxSymbol visitTimeEndByProcess(TimeEndByProcess process) {
    return CircusTimeConcreteSyntaxSymbol.DEADLINE_END_PROCESS;
  }

 public CircusTimeConcreteSyntaxSymbol visitTimeStartByProcess(TimeStartByProcess process) {
    return CircusTimeConcreteSyntaxSymbol.DEADLINE_START_PROCESS;
  }

public CircusTimeConcreteSyntaxSymbol visitTimeoutProcess(TimeoutProcess process) {
    return CircusTimeConcreteSyntaxSymbol.TIMEOUT_PROCESS;
  }


 public CircusTimeConcreteSyntaxSymbol visitTimedinterruptProcess(TimedinterruptProcess process) {
    return CircusTimeConcreteSyntaxSymbol.TIMEDINTERRUPT_PROCESS;
  }


 /* Support for Circus Time : Action */

 public CircusTimeConcreteSyntaxSymbol visitTimeEndByAction(TimeEndByAction action) {
    return CircusTimeConcreteSyntaxSymbol.DEADLINE_END_ACTION;
  }

 public CircusTimeConcreteSyntaxSymbol visitTimeStartByAction(TimeStartByAction action) {
    return CircusTimeConcreteSyntaxSymbol.DEADLINE_START_ACTION;
  }


 public CircusTimeConcreteSyntaxSymbol visitTimeoutAction(TimeoutAction action) {
    return CircusTimeConcreteSyntaxSymbol.TIMEOUT_ACTION;
  }


 public CircusTimeConcreteSyntaxSymbol visitTimedinterruptAction(TimedinterruptAction action) {
    return CircusTimeConcreteSyntaxSymbol.TIMEDINTERRUPT_ACTION;
  }

 public CircusTimeConcreteSyntaxSymbol visitWaitExprAction(WaitExprAction action) 
 {
	 if (action.isBasicWaitAction())
		    return CircusTimeConcreteSyntaxSymbol.WAIT_BASIC_ACTION;
	 else if (action.isWaitExprAction())
		    return CircusTimeConcreteSyntaxSymbol.WAIT_EXPR_ACTION;
	 else
		// TODO: think about a better exception to raise than this. Or perhaps something general coded up within PrefixingTimeAction?
			throw new IllegalArgumentException("Wait action doesn't have the right shape!");
  }

public CircusTimeConcreteSyntaxSymbol visitPrefixingTimeAction(PrefixingTimeAction action) {
	if (action.isAtPrefixingAction())
		return CircusTimeConcreteSyntaxSymbol.AT_PREFIX_ACTION;
	else if (action.isAtPrefixingExprAction())
		return CircusTimeConcreteSyntaxSymbol.AT_PREFIX_EXPR_ACTION;
	else if (action.isPrefixingExprAction())
		return CircusTimeConcreteSyntaxSymbol.PREFIX_EXPR_ACTION;
	else
		// TODO: think about a better exception to raise than this. Or perhaps something general coded up within PrefixingTimeAction?
		throw new IllegalArgumentException("Prefixing time action doesn't have the right shape!");
  }

  public interface Utils
    extends IsEmptyNameList
  {
  }

  public static class UtilsImpl
    extends StandardZ
    implements Utils
  {
  }
}
