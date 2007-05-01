/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circus.util;

import java.math.BigInteger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.CircusStateAnn;
import net.sourceforge.czt.circus.ast.Model;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.ParamQualifier;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.CircusFieldList;

/**
 *
 * @author leo
 */
public final class CircusUtils {
  
  /**
   * Do not create instances of this class.
   */
  private CircusUtils() {
  }

  /** The name of the Circus toolkit. */
  public static final String CIRCUS_TOOLKIT = "circus_toolkit";

  /**
   * Every basic process main action is named with this internal name.
   * Internal names start with a double dollar sign.
   * The typechecker must guaranttee that no such names are mentioned by the user.
   */
  public static final String DEFAULT_MAIN_ACTION_NAME = "$$mainAction";
  
  /**
   * Default name of state for stateless processes.
   */
  public static final String DEFAULT_PROCESS_STATE_NAME = "$$defaultSt"; 

  public static final String DEFAULT_IMPLICIT_ACTION_NAME_PREFIX = "$$implicitAct";
  public static final String DEFAULT_IMPLICIT_PROCESS_NAME_PREFIX = "$$implicitProc";
      
  /**
   * Default number of multisynchronisation occurrences for particular communication pattern.
   * At the moment this feature is still experimental, and may disapear in the future.
   */
  public static final BigInteger DEFAULT_MULTISYNCH = BigInteger.ZERO;

  /**
   * Default model for RefinementConjPara is failures-divergences.
   */    
  public static final Model DEFAULT_REFINEMENT_MODEL = Model.FlDv;

  /**
   * Default parameter qualifier for process and actions is by value.
   */
  public static final ParamQualifier DEFAULT_PARAMETER_QUALIFIER = ParamQualifier.Value; 
  
  /**
   * Returns true if the <code>ActionPara</code> is indeed a schema expression action 
   * with a non-null <code>Name</code>.
   */
  public static boolean isActionParaSchemaValid(ActionPara ap) {    
    return (ap.getName() != null) && 
           (ap.getCircusAction() instanceof SchExprAction);
  }
  
  /**
   * Checks whether the given <code>Para</code> term is a schema or not.
   * That is, it checks whether either: it is an <code>AxPara</code> term
   * properly encoded as either a horizontal or a boxed schema; or an
   * <code>ActionPara</code> term with a <code>SchExprAction</code>.
   */
  public static boolean isSchema(Para para) {
    boolean result = ZUtils.isSchema(para);
    if (!result) {
      // If it is not an AxPara schema, it can still be a SchExprAction one.
      result = (para instanceof ActionPara) &&
        (((ActionPara)para).getCircusAction() instanceof SchExprAction);
    }
    return result;
  }
  
  /**
   * If the given paragraph <code>isSchema(para)</code>, returns
   * the declared schema name. Otherwise, the method returns null.
   */
  public static Name getSchemaName(Para para)  {
    Name result = null;
    if (isSchema(para)) {
      result = ZUtils.getSchemaName(para);
      if (result == null) {
        ActionPara ap = (ActionPara)para;
        assert isActionParaSchemaValid(ap);
        result = ap.getName();
      }
    }
    return result;
  } 
  
  public static boolean isChannelFromDecl(ChannelDecl term) {
    return (term.getNameList() == null && term.getExpr() instanceof RefExpr);
  }
  
  public static boolean isOnTheFly(Term term) {
     // if it is already getCircusAction() with a annotation...
     boolean result = (term.getAnn(OnTheFlyDefAnn.class) != null);
     if (term instanceof ActionPara) {
         // else, check within the getCircusAction()
         ActionPara ap = (ActionPara)term;
         result = ap.getCircusAction().getAnn(OnTheFlyDefAnn.class) != null;
     }
     return result;
  }
  
  public static boolean isCircusState(Term term) {
     return term.getAnn(CircusStateAnn.class) != null;
  }
    
  public static CircusFieldList assertCircusFieldList(Term term) {
    if (term instanceof CircusFieldList) {
      return (CircusFieldList) term;
    }
    final String message = "Expected a CircusFieldList but found " + 
      String.valueOf(term);
    throw new UnsupportedAstClassException(message);    
  }        
  
  public static CircusFactoryImpl assertCircusFactoryImpl(Object factory) {
    if (factory instanceof CircusFactoryImpl) {
      return (CircusFactoryImpl) factory;
    }
    final String message = "Expected a CircusFactoryImpl but found " + 
      String.valueOf(factory);
    throw new UnsupportedAstClassException(message);    
  }
}
