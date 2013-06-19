/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.ohcircus.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.ohcircus.ast.OhCircusMethodPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.ProcessPara;

/**
 *
 * @author leo
 */
public final class OhCircusUtils
{

  /**
   * Do not create instances of this class.
   */
  private OhCircusUtils()
  {
  }
  public static final Factory FACTORY = new Factory();
  /** The name of the basic Circus toolkit. */
  public static final String OHCIRCUS_TOOLKIT = "ohcircus_toolkit";
  /** The name of the Circus prelude. */
  public static final String OHCIRCUS_PRELUDE = "ohcircus_prelude";
  
  /**
   * Concrete syntax symbol visitor that can be used everywhere.
   */
  public static final OhCircusConcreteSyntaxSymbolVisitor 
    OHCIRCUS_CONCRETE_SYNTAXSYMBOL_VISITOR = new OhCircusConcreteSyntaxSymbolVisitor();
  
  /**
   * Returns true if the <code>ActionPara</code> is indeed a schema expression action
   * with a non-null <code>Name</code>.
   */
  public static boolean isMethodParaSchemaValid(OhCircusMethodPara mp)
  {
    return (mp.getName() != null) &&
      (mp.getOhCircusMethod() instanceof SchExprAction);
  }
  
  /**
   * Checks whether the given <code>Para</code> term is a schema or not.
   * That is, it checks whether either: it is an <code>AxPara</code> term
   * properly encoded as either a horizontal or a boxed schema; or an
   * <code>ActionPara</code> term with a <code>SchExprAction</code>.
   */
  public static boolean isSimpleSchema(Para para)
  {
    boolean result = ZUtils.isSimpleSchema(para);
    if (!result)
    {
      // If it is not an AxPara schema, it can still be a SchExprAction one.
      result = (para instanceof OhCircusMethodPara) &&
        (((OhCircusMethodPara) para).getOhCircusMethod() instanceof SchExprAction);
    }
    return result;
  }

  
  public static boolean isOnTheFly(Term term)
  {
    // if it is already from a getCircusAction/Process() with an annotation...
    boolean result = (term.getAnn(OnTheFlyDefAnn.class) != null);

    // if not or if the term does not have an OnTheFlyDefAnn
    if (!result)
    {
      // select the appropriate element within a Para
      if (term instanceof ActionPara)
      {
        term = ((ActionPara) term).getCircusAction();
      } 
      else if (term instanceof OhCircusMethodPara)
      {
        term = ((OhCircusMethodPara) term).getOhCircusMethod();
      }
      else if (term instanceof ProcessPara)
      {
        term = ((ProcessPara) term).getCircusProcess();
      }
      result = term.getAnn(OnTheFlyDefAnn.class) != null;
    }
    return result;
  }
  
}
