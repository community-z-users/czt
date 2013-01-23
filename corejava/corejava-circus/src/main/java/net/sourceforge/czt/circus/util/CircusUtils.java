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
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusStateAnn;
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.Model;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.OutputFieldAnn;
import net.sourceforge.czt.circus.ast.ParamQualifier;
import net.sourceforge.czt.circus.ast.ProcessD;
import net.sourceforge.czt.circus.ast.ProofObligationAnn;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.util.ZString;
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
import net.sourceforge.czt.circus.ast.CircusNameSetList;
import net.sourceforge.czt.circus.ast.CircusChannelSetList;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.LocAnn;
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
  public static final String CIRCUS_TOOLKIT = Section.CIRCUS_TOOLKIT.getName();
  /** The name of the Circus prelude. */
  public static final String CIRCUS_PRELUDE = Section.CIRCUS_PRELUDE.getName();
  
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
  public static final String DEFAULT_IMPLICIT_DOTEXPR_NAME_PREFIX = "$$Dot";
  public static final String DEFAULT_IMPLICIT_NAMESET_NAME_PREFIX = "$$implicitNS";
  public static final String DEFAULT_IMPLICIT_CHANSET_NAME_PREFIX = "$$implicitCS";
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
  public static final ZName SYNCH_CHANNEL_TYPE_NAME = FACTORY.createZName(CircusString.CIRCUSSYNCH);
  
  /** Power type of the given type for synchronisation type names. ID is added to the synch name of this instance */
  public static final PowerType SYNCH_CHANNEL_TYPE = FACTORY.createPowerType(FACTORY.createGivenType(SYNCH_CHANNEL_TYPE_NAME));
  
  // look in the typechecker factory for a version with IDs
  public static final ZName TRANSFORMER_TYPE_NAME = FACTORY.createZName(CircusString.CIRCUSTRANSFORMER);  
  public static final PowerType TRANSFORMER_TYPE = FACTORY.createPowerType(FACTORY.createGivenType(TRANSFORMER_TYPE_NAME));

  /** Name for name and channel set maximal types (i.e., \power~$$CIRCUSID) - the ZName ID is added by type checker to this instance */
  public static final ZName CIRCUS_ID_TYPE_NAME = FACTORY.createZName(CircusString.CIRCUSID);
  
  /** Power type of the given type for synchronisation type names. ID is added to the synch name of this instance */
  public static final PowerType CIRCUS_ID_TYPE = FACTORY.createPowerType(FACTORY.createGivenType(CIRCUS_ID_TYPE_NAME));
  
  /** 
   *  Reference expression of the given type for synchronisation names. 
   *  An ID is added to the synch name of this instance. 
   *  
   *  This expression is not typed, even after the typechecker is created.  
   *  If one creates synchronisation channels on-the-fly, one MUST type
   *  check it before use in order to add  the proper powertype to the 
   *  synch_channeel_expr used.
   */
  public static final RefExpr SYNCH_CHANNEL_EXPR = FACTORY.createRefExpr(SYNCH_CHANNEL_TYPE_NAME);
  public static final RefExpr CIRCUS_ID_EXPR = FACTORY.createRefExpr(CIRCUS_ID_TYPE_NAME);
  public static final RefExpr TRANSFORMER_EXPR = FACTORY.createRefExpr(TRANSFORMER_TYPE_NAME);

  /**
   * Concrete syntax symbol visitor that can be used everywhere.
   */
  public static final CircusConcreteSyntaxSymbolVisitor 
    CIRCUS_CONCRETE_SYNTAXSYMBOL_VISITOR = new CircusConcreteSyntaxSymbolVisitor();
  
  /**
   * Returns true if the <code>ActionPara</code> is indeed a schema expression action
   * with a non-null <code>Name</code>.
   */
  public static boolean isActionParaSchemaValid(ActionPara ap)
  {
    return (ap.getName() != null) &&
      (ap.getCircusAction() instanceof SchExprAction);
  }
  
  public static boolean isOutputField(Term term)
  {
    return (term instanceof DotField && 
            term.getAnn(OutputFieldAnn.class) != null);
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
      result = (para instanceof ActionPara) &&
        (((ActionPara) para).getCircusAction() instanceof SchExprAction);
    }
    return result;
  }

  /**
   * If the given paragraph <code>isSimpleSchema(para)</code>, returns
   * the declared schema name. Otherwise, the method returns null.
   */
  public static Name getSchemaName(Para para)
  {
    Name result = null;
    if (isSimpleSchema(para) || ZUtils.isHorizontalDef(para))
    {
      AxPara axp = (AxPara) para;
      assert ZUtils.isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getName();
      if (result == null)
      {
        ActionPara ap = (ActionPara) para;
        assert isActionParaSchemaValid(ap);
        result = ap.getName();
      }
    }
    return result;
  }
  
  public static boolean isChannelFrom(Term term)
  {
    boolean result = (term instanceof ChannelDecl);
    if (result)
    {        
      result = (((ChannelDecl)term).getNameList().size() > 1 &&
              ((ChannelDecl)term).getNameList().get(1) instanceof ZNameList);
      if (result)
      {
        result = ((ChannelDecl)term).getZChannelNameList().isEmpty();
      }      
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
      else if (term instanceof ProcessPara)
      {
        term = ((ProcessPara) term).getCircusProcess();
      }
      result = term.getAnn(OnTheFlyDefAnn.class) != null;
    }
    return result;
  }

  public static boolean isStatePara(Term term)
  {
    return term.getAnn(CircusStateAnn.class) != null;
  }

  public static boolean isCircusInnerProcessPara(Para term)
  {
    return !ZUtils.isZPara(term) &&
      ((term instanceof ActionPara) ||
      (term instanceof NameSetPara) ||
      ((term instanceof TransformerPara) &&
      ((TransformerPara) term).getTransformerPred() instanceof ActionTransformerPred));
  }

  public static boolean isCircusGlobalPara(Para term)
  {
    return !ZUtils.isZPara(term) &&
      ((term instanceof ChannelPara) ||
      (term instanceof ProcessPara) ||
      (term instanceof ChannelSetPara) ||
      ((term instanceof TransformerPara) &&
      ((TransformerPara) term).getTransformerPred() instanceof ProcessTransformerPred));
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
  public static Map<ZName, CircusProcess> getZSectImplicitProcessPara(ZSect term)
  {
    HashMap<ZName, CircusProcess> result = new HashMap<ZName, CircusProcess>();
    ZParaList implicitProcPara = getZSectImplicitProcessParaList(term.getName(),
      term.getZParaList());
    for (Para p : implicitProcPara)
    {
      if (!(p instanceof ProcessPara))
      {
        throw new UnsupportedAstClassException("Unsupported on-the-fly paragraph class " + p.getClass().
          getName() + " within ZSect" + term.getName());
      }
      ProcessPara pp = (ProcessPara) p;

      CircusProcess old = result.put(pp.getZName(), pp.getCircusProcess());
      if (old != null)
      {
        throw new UnsupportedAstClassException("Duplicated name for on-the-fly process definition with ZSect" +
          term.getName() + ": " + pp.getZName());
      }
    }
    return result;
  }

  public static ZParaList /*List<ProcessPara>*/ getZSectImplicitProcessParaList(String sectName,
    ZParaList term)
  {
    ZParaList result = FACTORY.createZParaList();
    for (Para p : term)
    {
      if ((p instanceof ProcessPara) &&
        ((ProcessPara) p).getZName().getWord().startsWith(DEFAULT_IMPLICIT_PROCESS_NAME_PREFIX))
      {
        ProcessPara pp = (ProcessPara) p;

        if (pp.getCircusProcess().getAnn(OnTheFlyDefAnn.class) == null)
        {
          throw new UnsupportedAstClassException("Invalid on-the-fly process definition within ZSect " + sectName);
        }
        if (pp.getZGenFormals() != null && !pp.getZGenFormals().isEmpty())
        {
          throw new UnsupportedAstClassException("On-the-fly process definition within ZSect " + sectName + " cannot have formal generic parameters.");
        }

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
  
  public static CircusChannelSetList assertCircusChannelSetList(Term term)
  {
    if (term instanceof CircusChannelSetList)
    {
      return (CircusChannelSetList) term;
    }
    final String message =
      "Expected a CircusChannelSetList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static CircusNameSetList assertCircusNameSetList(Term term)
  {
    if (term instanceof CircusNameSetList)
    {
      return (CircusNameSetList) term;
    }
    final String message =
      "Expected a CircusNameSetList but found " + String.valueOf(term);
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
   *    <li><code>CommPattern.Output</code> if the list of fields is not empty and contain instances of either <code>DotField</code>.
   *    <li><code>CommPattern.Mixed</code> if the list of fields is not empty and contain at least one <code>InputField</code> and either one <code>DotField</code>.
   *    <li><code>CommPattern.Mixed</code> with a parser error if the list of fields is not empty but neither of the above patterns hold.
   * </ul>
   * </p>
   */
  public static CommPattern retrieveCommPattern(List<Field> fields)
  {
    CommPattern result = null;
    if (fields.isEmpty())
    {
      result = CommPattern.Synch;
    }
    else
    {
      int input = 0;
      int output = 0;
      for (Field f : fields)
      {
        if (f instanceof InputField)
        {
          input++;
        }
        else if (f instanceof DotField)
        {
          output++;
        }
      }
      if (input > 0 && output > 0)
      {
        result = CommPattern.Mixed;
      }
      else if (input > 0 && output == 0)
      {
        result = CommPattern.Input;
      }
      else if (input == 0 && output > 0)
      {
        result = CommPattern.Output;
      }
    }
    assert result != null :
      "Invalid communication pattern. The communication is neither of synchronisation, " +
      "input, output, or mixed pattern format. This can only happen with specialised " +
      "implementations of Field that do not obbey follow any available CommPattern type, " +
      "and should never happen.";
    return result;
  }  
  
  public static void addProofObligationAnn(Term term, Pred pred)  
  {
    assert term != null && pred != null;
    ProofObligationAnn poAnn = (ProofObligationAnn) term.getAnn(ProofObligationAnn.class);
    if (poAnn == null)
    {
      poAnn = FACTORY.createProofObligationAnn(pred);
      term.getAnns().add(poAnn);
    }
    else
    {
      poAnn.setPred(pred);
    }
  }
  
  private static final String ANONYMOUS_PATTERN        = "Anonymous";  
  private static final String FULLNAME_LINE_COLUMN     = "{0}_L{1}C{2}";
  private static final String FULLNAME_LOC_LINE_COLUMN = "{0}_F{{1})L{2}C{3}";
  private static final String FULLNAME_UNIQUE_ID       = "{0}_{1}";  
  private static int fullNameUniqueId_ = 0;
  
  public static String createFullQualifiedName(String name, int idSeed)
  {
    String pattern = FULLNAME_UNIQUE_ID;
    List<String> params = new ArrayList<String>(2);
    params.add(name);
    params.add(String.valueOf(idSeed));
    return MessageFormat.format(pattern, params.toArray());
  }
  
  public static String createFullQualifiedName(String name, LocAnn loc, boolean usePhysicalLoc)
  {
    String pattern, result;
    if (loc != null)
    {
      List<String> params = new ArrayList<String>();
      params.add(name);
      pattern = FULLNAME_LINE_COLUMN;
      params.add(loc.getLine().toString());
      params.add(loc.getCol().toString());      
      if (usePhysicalLoc)
      {
        params.add(1, loc.getLoc());
        pattern = FULLNAME_LOC_LINE_COLUMN;
      }      
      result = MessageFormat.format(pattern, params.toArray());
    }
    else
    {
      result = createFullQualifiedName(name, fullNameUniqueId_);      
      fullNameUniqueId_++;
    }
    return result;
  }
  
  public static String createFullQualifiedName(String name, LocAnn loc)
  {
    return createFullQualifiedName(name, loc, false);
  }
  
  public static String createFullQualifiedName(String name)
  {
    return createFullQualifiedName(name, null, false);
  }
  
  public static String createAnonymousName()
  {
    return createFullQualifiedName(ANONYMOUS_PATTERN);
  }
  
  /**
   * Creates a fully qualified name according to the location annotation
   * information, if avaiable. It also considers the LocAnn.getLoc() value if
   * usePhysicalLoc is true. If the name has no LocAnn (e.g., names created
   * by a prover window), a unique number ID is given
   * @param name
   * @param usePhysicalLoc
   * @return
   */
  public static ZName createFullQualifiedName(ZName name, boolean usePhysicalLoc)
  {
    LocAnn loc = (LocAnn)name.getAnn(LocAnn.class);        
    String qualifiedName = createFullQualifiedName(name.getWord(), loc, usePhysicalLoc);
    
    // create a name with the same ID
    ZName result = FACTORY.createZName(name);
    
    // append to the name getWord() the fully qualified pattern
    result.setWord(qualifiedName);
    
    return result;
  }
  
  /**
   * Calls createFullQualifiedName with the name and false for usePhysicalLoc
   * @param name
   * @return
   */
  public static ZName createFullQualifiedName(ZName name)
  {
    return createFullQualifiedName(name, false);
  }
  
  public static ZName createAnonymousZName()
  {
    String qualifiedName = createFullQualifiedName(createAnonymousName(), null, false);    
    // create a name with the same ID
    ZName result = FACTORY.createZName(qualifiedName);
    return result;
  }
  
  public static ZName qualifyName(ZName first, ZName second)
  {
    ZName result = createFullQualifiedName(first);
    
    // make the full qualified name id the second name id
    // if not null - otherwise the first is used already.
    if (second.getId() != null)
    {     
      result.setId(second.getId());
    }
    
    result.setWord(result.getWord() + ZString.DOT + second.getWord());
    
    return result;
  }
  
  public static boolean isBasicProcess(Term term)
  {
    boolean result = (term instanceof BasicProcess);
    if (!result)
    {
      result = ((term instanceof ProcessD) && ((ProcessD)term).isBasicProcess());
    }
    return result;      
  }
  
  public static BasicProcess getBasicProcess(Term term)
  {
    BasicProcess result = null;
    if (isBasicProcess(term))
    {
      if (term instanceof BasicProcess)
        result = (BasicProcess)term;
      else if (term instanceof ProcessD)
        result = ((ProcessD)term).getCircusBasicProcess();
    }
    return result;
  }
  
  private static ZName booleanName_ = FACTORY.createZName(CircusString.BOOLEAN);
  public static boolean isBooleanType(Object obj)
  {
    boolean result = (obj instanceof GivenType);
    if (result)
    {
      GivenType gt = (GivenType)obj;      
      result = ZUtils.namesEqual(gt.getName(), booleanName_);
    }
    return result;
  }
  
  /**
   * Determines whether this communication is implicitly generically typed.
   * That is, its channel reference was declared with a generic type and no
   * generic actuals had been given (e.g., [X] gen \in X; gen.0).
   * 
   * To check this, it relies on a type annotation for the term. 
   * If not present, the result is null and can't be deduced. 
   * If present, the result accurately determines 
   * @return 
   */  
//  public static Boolean isImplicitlyGenericallyTyped(Communication term)
//  {
//    Boolean result = null;
//    TypeAnn typeAnn = term.getAnn(TypeAnn.class);
//    if (typeAnn != null)
//    {
//      term.getChannelExpr().getZExprList().isEmpty();
//      if (typeAnn.getType() instanceof CommunicationType)
//      {
//        CommunicationType commType = (CommunicationType)typeAnn.getType();
//        commType.
//      }
//      else
//    }
//    boolean result = typeAnn != null typeAnn.getType() instanceof GenericType
//    !term.getChannelExpr().getExplicit()
//    !getChannelExpr().getExplicit() &&
//    getChannelExpr().getZExprList().isEmpty()
//  }

}
