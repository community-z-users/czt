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


  public CircusTimeConcreteSyntaxSymbol visitWaitAction(WaitAction action) {
    return CircusTimeConcreteSyntaxSymbol.WAIT_ACTION;
  }


 public CircusTimeConcreteSyntaxSymbol visitWaitRangeAction(WaitRangeAction action) {
    return CircusTimeConcreteSyntaxSymbol.WAIT_RANGE_ACTION;
  }


public CircusTimeConcreteSyntaxSymbol visitPrefixingExprAction(PrefixingExprAction action) {
    return CircusTimeConcreteSyntaxSymbol.PREFIX_EXPR_ACTION;
  }

public CircusTimeConcreteSyntaxSymbol visitAtPrefixingAction(AtPrefixingAction action) {
    return CircusTimeConcreteSyntaxSymbol.AT_PREFIX_ACTION;
  }

public CircusTimeConcreteSyntaxSymbol visitAtPrefixingExprAction(AtPrefixingExprAction action) {
    return CircusTimeConcreteSyntaxSymbol.AT_PREFIX_EXPR_ACTION;
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
