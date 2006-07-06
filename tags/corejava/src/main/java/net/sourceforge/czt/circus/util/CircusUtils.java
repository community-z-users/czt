/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circus.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.DeclName;
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
  
  /**
   * Returns true if the <code>ActionPara</code> is indeed a schema expression action 
   * with a non-null <code>DeclName</code>.
   */
  public static boolean isActionParaSchemaValid(ActionPara ap) {    
    return (ap.getDeclName() != null) && 
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
  public static DeclName getSchemaName(Para para)  {
    DeclName result = null;
    if (isSchema(para)) {
      result = ZUtils.getSchemaName(para);
      if (result == null) {
        ActionPara ap = (ActionPara)para;
        assert isActionParaSchemaValid(ap);
        result = ap.getDeclName();
      }
    }
    return result;
  } 
    
  public static CircusFieldList assertCircusFieldList(Term term) {
    if (term instanceof CircusFieldList) {
      return (CircusFieldList) term;
    }
    final String message = "Expected a CircusFieldList but found " + 
      String.valueOf(term);
    throw new UnsupportedAstClassException(message);    
  }        
}
