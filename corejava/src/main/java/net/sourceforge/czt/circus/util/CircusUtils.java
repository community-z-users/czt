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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.CircusStateAnn;
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.Model;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.ParamQualifier;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionTransformerPred;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.CircusFieldList;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessTransformerPred;
import net.sourceforge.czt.z.ast.ZName;

/**
 *
 * @author leo
 */
public final class CircusUtils
{
  
  /**
   * Do not create instances of this class.
   */
  private CircusUtils()
  {
  }
  
  public static final Factory FACTORY = new Factory();
  
  /** The name of the basic Circus toolkit. */
  public static final String CIRCUS_TOOLKIT = "circus_toolkit";
  
  /** The name of the Circus prelude. */
  public static final String CIRCUS_PRELUDE = "circus_prelude";
  
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
  
  public static final String DEFAULT_IMPLICIT_DOTEXPR_NAME_PREFIX = "$$!";
    
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
  
  /* NOTE: add the type for SYNCH given type. The OZ typechecker uses
   *       a special OIDType AST class. I will assume this is not needed for us.
   */ 
  
  /** Name for synchronisation channel type (ID is added by type checker to this instance */
  public static final ZName SYNCH_CHANNEL_NAME = FACTORY.createZName(CircusString.CIRCUSSYNCH);
  
  /** Power type of the given type for synchronisation type names. ID is added to the synch name of this instance */
  public static final PowerType SYNCH_CHANNEL_TYPE = FACTORY.createPowerType(FACTORY.createGivenType(SYNCH_CHANNEL_NAME)); 
  
  /** 
   *  Reference expression of the given type for synchronisation names. 
   *  An ID is added to the synch name of this instance. 
   *  
   *  This expression is not typed, even after the typechecker is created.  
   *  If one creates synchronisation channels on-the-fly, one MUST type
   *  check it before use in order to add  the proper powertype to the 
   *  synch_channeel_expr used.
   */
  public static final RefExpr SYNCH_CHANNEL_EXPR = FACTORY.createRefExpr(SYNCH_CHANNEL_NAME); 

  /**
   * Returns true if the <code>ActionPara</code> is indeed a schema expression action
   * with a non-null <code>Name</code>.
   */
  public static boolean isActionParaSchemaValid(ActionPara ap)
  {
    return (ap.getName() != null) &&
      (ap.getCircusAction() instanceof SchExprAction);
  }
  
  /**
   * Checks whether the given <code>Para</code> term is a schema or not.
   * That is, it checks whether either: it is an <code>AxPara</code> term
   * properly encoded as either a horizontal or a boxed schema; or an
   * <code>ActionPara</code> term with a <code>SchExprAction</code>.
   */
  public static boolean isSchema(Para para)
  {
    boolean result = ZUtils.isSchema(para);
    if (!result)
    {
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
  public static Name getSchemaName(Para para)
  {
    Name result = null;
    if (isSchema(para) || ZUtils.isHorizontalDef(para))
    {
      result = ZUtils.getSchemaName(para);
      if (result == null)
      {
        ActionPara ap = (ActionPara)para;
        assert isActionParaSchemaValid(ap);
        result = ap.getName();
      }
    } 
    return result;
  }
  
  public static boolean isChannelFromDecl(ChannelDecl term)
  {
    return (term.getNameList() == null && term.getExpr() instanceof RefExpr);
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
        term = ((ActionPara)term).getCircusAction();
      }
      else if (term instanceof ProcessPara)
      {
        term = ((ProcessPara)term).getCircusProcess();
      }      
      result = term.getAnn(OnTheFlyDefAnn.class) != null;      
    }
    return result;
  }
  
  public static boolean isCircusState(Term term)
  {
    return term.getAnn(CircusStateAnn.class) != null;
  }
  
  public static boolean isCircusInnerProcessPara(Para term)
  {
    return !ZUtils.isZPara(term) &&
      ((term instanceof ActionPara) ||
      (term instanceof NameSetPara) ||
      ((term instanceof TransformerPara) &&
      ((TransformerPara)term).getTransformerPred() instanceof ActionTransformerPred));
  }
  
  public static boolean isCircusGlobalPara(Para term)
  {
    return !ZUtils.isZPara(term) &&
      ((term instanceof ChannelPara) ||
      (term instanceof ProcessPara) ||
      (term instanceof ChannelSetPara) ||
      ((term instanceof TransformerPara) &&
      ((TransformerPara)term).getTransformerPred() instanceof ProcessTransformerPred));
  }     

  /**
   * From a given ZSect term, this method extract all the implicitly declared 
   * CircusProcess definitions, which are associated with the corresponding 
   * names in the map. If duplicated names are found, process paragraphs with 
   * CircusProcess definitions not marked as on-the-flyor, or on-the-fly 
   * processes with formal generic parameters, this method throws an
   * UnsupportedAstClassException. These situations should never happen wihtin
   * a well-implemented parser/typechecker.
   */
  public static Map<ZName, CircusProcess> getZSectImplicitProcessPara(ZSect term) {
    HashMap<ZName, CircusProcess> result = new HashMap<ZName, CircusProcess>();
    ZParaList implicitProcPara = getZSectImplicitProcessParaList(term);
    for (Para p : implicitProcPara) {
      if (!(p instanceof ProcessPara))
        throw new UnsupportedAstClassException("Unsupported on-the-fly paragraph class " + p.getClass().getName() + " within ZSect" + term.getName());
      ProcessPara pp = (ProcessPara)p;
      
      CircusProcess old = result.put(pp.getZName(), pp.getCircusProcess());
      if (old != null)
        throw new UnsupportedAstClassException("Duplicated name for on-the-fly process definition with ZSect" + 
            term.getName() +": " + pp.getZName());      
    }    
    return result;
  }
    
  public static ZParaList /*List<ProcessPara>*/ getZSectImplicitProcessParaList(ZSect term) 
  {
    ZParaList result = FACTORY.createZParaList();        
    for(Para p : term.getZParaList()) {
      if ((p instanceof ProcessPara) && 
         ((ProcessPara)p).getZName().getWord().startsWith(DEFAULT_IMPLICIT_PROCESS_NAME_PREFIX)) 
      {
        ProcessPara pp = (ProcessPara)p;
        
        if (pp.getCircusProcess().getAnn(OnTheFlyDefAnn.class) == null) 
          throw new UnsupportedAstClassException("Invalid on-the-fly process definition within ZSect " + term.getName());      
        if (pp.getZGenFormals() != null && !pp.getZGenFormals().isEmpty()) 
          throw new UnsupportedAstClassException("On-the-fly process definition within ZSect " + term.getName() + " cannot have formal generic parameters.");      
        
        result.add(pp);
      }
    }
    return result;
  }
  
  public static CircusFieldList assertCircusFieldList(Term term)
  {
    if (term instanceof CircusFieldList)
    {
      return (CircusFieldList) term;
    }
    final String message = "Expected a CircusFieldList but found " +
      String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static CircusFactoryImpl assertCircusFactoryImpl(Object factory)
  {
    if (factory instanceof CircusFactoryImpl)
    {
      return (CircusFactoryImpl) factory;
    }
    final String message = "Expected a CircusFactoryImpl but found " +
      String.valueOf(factory);
    throw new UnsupportedAstClassException(message);
  }
  
  public static ActionTransformerPred assertActionTransformerPred(Term term)
  {
    if (term instanceof ActionTransformerPred)
    {
      return (ActionTransformerPred) term;
    }
    final String message =
      "Expected a ActionTransformerPred but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static ProcessTransformerPred assertProcessTransformerPred(Term term)
  {
    if (term instanceof ProcessTransformerPred)
    {
      return (ProcessTransformerPred) term;
    }
    final String message =
      "Expected a ActionTransformerPred but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static CircusCommunicationList assertCircusCommunicationList(Term term)
  {
    if (term instanceof CircusCommunicationList)
    {
      return (CircusCommunicationList) term;
    }
    final String message =
      "Expected a CircusCommunicationList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  /**
   * <p>
   * Returns the communication type based on the pattern of the given list of communication fields.
   * </p>
   * <p>
   * It returns: 
   * <ul>
   *    <li><code>CommPattern.Synch</code> if the list of fields is empty.
   *    <li><code>CommPattern.Input</code> if the list of fields is not empty and contain only instances of <code>InputField</code>.
   *    <li><code>CommPattern.Output</code> if the list of fields is not empty and contain instances of either <code>DotField</code> or <code>OutputField</code>.
   *    <li><code>CommPattern.Mixed</code> if the list of fields is not empty and contain at least one <code>InputField</code> and either one <code>DotField</code> or one <code>OutputField</code>.
   *    <li><code>CommPattern.Mixed</code> with a parser error if the list of fields is not empty but neither of the above patterns hold.
   * </ul>
   * </p>
   */
    public static CommPattern retrieveCommPattern(List<Field> fields) {
      CommPattern result = null;
      if (fields.isEmpty()) {
        result = CommPattern.Synch;
      } else {        
        int input = 0;
        int output = 0;
        for (Field f : fields) {
          if (f instanceof InputField)
            input++;
          else if (f instanceof DotField)
            output++;
        }
        if (input > 0 && output > 0)
          result = CommPattern.Mixed;
        else if (input > 0 && output == 0)
          result = CommPattern.Input;
        else if (input == 0 && output > 0)
          result = CommPattern.Output;                        
      }
      assert result != null : 
        "Invalid communication pattern. The communication is neither of synchronisation, " +
        "input, output, or mixed pattern format. This can only happen with specialised " +
        "implementations of Field that do not obbey follow any available CommPattern type, " +
        "and should never happen.";
      return result;
    }
}
