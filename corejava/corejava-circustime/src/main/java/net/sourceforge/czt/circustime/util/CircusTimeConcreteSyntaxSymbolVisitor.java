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

  /* Support for Circus Time */
  public CircusTimeConcreteSyntaxSymbol visitTimeoutAction(TimeoutAction action) {
    return CircusTimeConcreteSyntaxSymbol.TIMEOUT_ACTION;
  }

  public CircusTimeConcreteSyntaxSymbol visitWaitAction(WaitAction action) {
    return CircusTimeConcreteSyntaxSymbol.WAIT_ACTION;
  }

  public CircusTimeConcreteSyntaxSymbol visitDeadlineAction(DeadlineAction action) {
    return CircusTimeConcreteSyntaxSymbol.DEADLINE_ACTION;
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
