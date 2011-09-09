/*
 * ZPrinter.java
 *
 * Created on 15 September 2005, 11:08
 */
package net.sourceforge.czt.zeves.z;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZExprListVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ZEvesIncompatibleASTException;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.Assoc;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.BindSelExpr;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.Cat;
import net.sourceforge.czt.z.ast.CompExpr;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Expr;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.ForallExpr;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.HideExpr;
import net.sourceforge.czt.z.ast.IffExpr;
import net.sourceforge.czt.z.ast.IffPred;
import net.sourceforge.czt.z.ast.ImpliesExpr;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.LetExpr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.MuExpr;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Operand;
import net.sourceforge.czt.z.ast.Operator;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PipeExpr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Pred2;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.ProjExpr;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.StrokeList;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.TupleSelExpr;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZRenameList;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.OperatorName.Fixity;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BindExprVisitor;
import net.sourceforge.czt.z.visitor.BindSelExprVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.NewOldPairVisitor;
import net.sourceforge.czt.z.visitor.QntExprVisitor;
import net.sourceforge.czt.z.visitor.SetCompExprVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.DeclVisitor;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.FalsePredVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.HideExprVisitor;
import net.sourceforge.czt.z.visitor.InStrokeVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NegPredVisitor;
import net.sourceforge.czt.z.visitor.NextStrokeVisitor;
import net.sourceforge.czt.z.visitor.NumStrokeVisitor;
import net.sourceforge.czt.z.visitor.OutStrokeVisitor;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.PowerExprVisitor;
import net.sourceforge.czt.z.visitor.Pred2Visitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchExpr2Visitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SchTextVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZRenameListVisitor;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationKind;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.QuantifiersCommand;
import net.sourceforge.czt.zeves.ast.SimplificationCommand;
import net.sourceforge.czt.zeves.ast.SubstitutionCommand;
import net.sourceforge.czt.zeves.ast.UseCommand;
import net.sourceforge.czt.zeves.ast.WithCommand;
import net.sourceforge.czt.z.visitor.CondExprVisitor;
import net.sourceforge.czt.z.visitor.LambdaExprVisitor;
import net.sourceforge.czt.z.visitor.LetExprVisitor;
import net.sourceforge.czt.z.visitor.MuExprVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.NegExprVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.PreExprVisitor;
import net.sourceforge.czt.z.visitor.ProdExprVisitor;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.TupleSelExprVisitor;
import net.sourceforge.czt.zeves.ast.LabelAbility;
import net.sourceforge.czt.zeves.ast.LabelUsage;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.util.ZEvesString;
import net.sourceforge.czt.zeves.util.ZEvesUtils;
import net.sourceforge.czt.zeves.visitor.ApplyCommandVisitor;
import net.sourceforge.czt.zeves.visitor.CaseAnalysisCommandVisitor;
import net.sourceforge.czt.zeves.visitor.InstantiationListVisitor;
import net.sourceforge.czt.zeves.visitor.InstantiationVisitor;
import net.sourceforge.czt.zeves.visitor.NormalizationCommandVisitor;
import net.sourceforge.czt.zeves.visitor.ProofCommandVisitor;
import net.sourceforge.czt.zeves.visitor.ProofScriptVisitor;
import net.sourceforge.czt.zeves.visitor.QuantifiersCommandVisitor;
import net.sourceforge.czt.zeves.visitor.SimplificationCommandVisitor;
import net.sourceforge.czt.zeves.visitor.SubstitutionCommandVisitor;
import net.sourceforge.czt.zeves.visitor.UseCommandVisitor;
import net.sourceforge.czt.zeves.visitor.WithCommandVisitor;

/**
 * <p>
 * This class converts CZT terms, more precisely Para, Expr, or Pred, to Z/Eves
 * socket server XML API. Every visiting method returns a string with the corresponding
 * production.
 * </p>
 * <p>
 * As Z/Eves is not compliant with the Z standard, we needed to adapt and adjust
 * the parts where incompatibilities arise. For instante, for the labelled-predicate
 * or schema-ref instead of schema-expression in schema inclusions.
 * Whenever such incompatibility occurs, a ZEvesIncompatibleASTException is thrown
 * with detailed information and additional throwable cause for the problem.
 * </p>
 * <p>
 * On the other hand, Z/Eves Z also includes additional information, such as labels and
 * proof script for conjectures, ability and usage for automation pursposes, and so on.
 * In this situations where there is no Z standard correspondent from the CZT AST, we
 * provided annotations with the necessary information. We expect these annotations to
 * be added to the terms via some sort of visual interface.
 * </p>
 * <p>
 * The method of interest is called print, which accepts a term. One can also alter
 * the current section manager, which at the moment is not being used for anything.
 * At a later stage, it will be used for recognising Parent sections and most importantly
 * the Z toolkit. At the moment, we just include a naive translation of most common operators.
 * </p>
 * 
 * @author leo, 20/09/2005
 * @since 1.5
 */
public class CZT2ZEvesPrinter extends BasicZEvesTranslator implements
        /* Special visitors */
        TermVisitor<String>, FreetypeVisitor<String>, SchTextVisitor<String>,
        ZNameVisitor<String>,
        /* Z List visitors */
        ZDeclListVisitor<String>, ZExprListVisitor<String>, ZNameListVisitor<String>,
        /* Stroke visitors */
        StrokeVisitor<String>, NumStrokeVisitor<String>, NextStrokeVisitor<String>,
        InStrokeVisitor<String>, OutStrokeVisitor<String>,
        /* Paragraphs visitors */
        GivenParaVisitor<String>, AxParaVisitor<String>, FreeParaVisitor<String>,
        ConjParaVisitor<String>, ParaVisitor<String>, NarrParaVisitor<String>,
        LatexMarkupParaVisitor<String>, UnparsedParaVisitor<String>,
        /* Declaration visitors */
        VarDeclVisitor<String>, /*ConstDeclVisitor<String>,*/
        InclDeclVisitor<String>, DeclVisitor<String>,
        /* Predicate visitors */
        TruePredVisitor<String>, FalsePredVisitor<String>, NegPredVisitor<String>,
        QntPredVisitor<String>, Pred2Visitor<String>, /*AndPredVisitor<String>,*/
        MemPredVisitor<String>, ExprPredVisitor<String>, PredVisitor<String>,
        /* Expression visitors */
        ExprVisitor<String>, RefExprVisitor<String>, PowerExprVisitor<String>,
        ProdExprVisitor<String>, SetExprVisitor<String>, SetCompExprVisitor<String>,
        NumExprVisitor<String>, TupleExprVisitor<String>,
        TupleSelExprVisitor<String>, QntExprVisitor<String>, /*Qnt1ExprVisitor<String>, */ LambdaExprVisitor<String>,
        MuExprVisitor<String>, LetExprVisitor<String>, NegExprVisitor<String>, CondExprVisitor<String>,
        PreExprVisitor<String>, ThetaExprVisitor<String>, BindSelExprVisitor<String>,
        BindExprVisitor<String>, SchExprVisitor<String>, SchExpr2Visitor<String>,
        HideExprVisitor<String>, ApplExprVisitor<String>, DecorExprVisitor<String>, 
        RenameExprVisitor<String>, ZRenameListVisitor<String>, NewOldPairVisitor<String>,
        /* Proof command visitors */
        ProofCommandVisitor<String>, CaseAnalysisCommandVisitor<String>,
        NormalizationCommandVisitor<String>, QuantifiersCommandVisitor<String>,
        InstantiationVisitor<String>, InstantiationListVisitor<String>,
        SimplificationCommandVisitor<String>, UseCommandVisitor<String>,
        WithCommandVisitor<String>, SubstitutionCommandVisitor<String>,
        ApplyCommandVisitor<String>, ProofScriptVisitor<String>, OptempParaVisitor<String>
{

  /**
   * CZT Section manger object.
   */
  private SectionInfo fSectionInfo;
  
  /**
   * Current section name
   */
  private String fSectionName = null;
  
  /**
   * Label annotations matter only for axiomatic and generic boxes.
   * The flag switches its processing on and off.
   */
  private boolean fCheckForLabelAnnotations = false;

  /**
   * Flag set at getRel(term) method in order to instruct reference visiting
   * to consider operator names as relational applications.
   * That is, when the flag is true, the translation considers "x \\leq y"
   * as  "x &leq; y", whereas when the flag is false, the translation considers
   * "(\\_ \\leq \\_)~(x, y)". In other words, the former just translates the
   * operator symbol, whereas the second translates both the operator symbol
   * as well as the underscore ARG_TOK.
   *
   * We could have used a stack, but there is no need. The only convoluted case
   * is for ApplExpr within another (e.g., x \cup y \cap z), in which case the
   * chaining will guarantee the flag is set properly. The other cases RefExpr
   * and DeclLists cannot have chained operators.
   *
   * ApplExpr->RefExpr->ApplExpr could be one such case. Have a stack, then there
   * is no need for the other flag (e.g., just check the stack top contents to see
   * which case it is: keep args or not).
   *
   * When to add ARG_TOK or not depends on the stack state. Stack tops with SchText
   * or (ZName with valid getOperatorName()) should add ARGS, whereas all other terms
   * shouldn't. As complicated optemp patterns keep cropping up, we also allow a "boolean"
   * to be added to the stack. If true, then ARG_TOK; if false, no.
   *
   */
  private final Stack<Object> fRelationalOpAppl;

  /**
   * In certain cases of RelationalOpAppl we also want to keep the ARG_TOK, like
   * in DeclList of Sch/AxDef, for definition of operator templates. We don't need
   * them for the operator being applied, though.
   */
  //private boolean fKeepOpArgs = false;

  /**
   * Separation string for expressions in a ZExprList (used during visitZExprList)
   */
  private String fZExprListSep = null;

  /**
   * Current instantiation kind (used during visitQuantifiersCommand and visitUseCommand).
   * Because of renaming expressions, we need a stack here (e.g., A[x := B[y := z], y := a]).
   */
  private final Stack<InstantiationKind> fCurrInstKind;

  /**
   * Map containing proof command lists for corresponding theorem names.
   * They can be used for both batch mode proof as well as interactive
   */
  private final Map<String, List<String>> proofScripts_;

  /**
   * Top-level printer for specification terms (e.g., ZSect, NarrSect, etc).
   * It is a printer as a list of strings, instead of a single string.
   */
  private final SpecPrinter fSpecPrinter;
  
  /* Constructors */
  /** Creates a new instance of ZPrinter
   * @param si
   */
  public CZT2ZEvesPrinter(SectionInfo si)
  {
    super();
    fSectionName = null;
    fSectionInfo = null;
    fZExprListSep = null;
    //fKeepOpArgs = false;
    fCurrInstKind = new Stack<InstantiationKind>();
    fRelationalOpAppl = new Stack<Object>();
    fCheckForLabelAnnotations = false;
    fSpecPrinter = new SpecPrinter();
    proofScripts_ = new TreeMap<String, List<String>>();
    setSectionInfo(si);
  }

  /* Auxiliary Methods */
  /**
   * Throws a ZEvesIncompatibleASTException due to empty declaration on paragraph boxes.
   */
  private void emptyDeclPartException()
  {
    throw new ZEvesIncompatibleASTException("Z/Eves does not accept empty declarations on paragraph boxes or binding expressions");
  }

  /**
   * Checks whether the inclusion expression is valid or not, providing
   * detailed information in the case it is. If it is valid, this method
   * returns null meaning there is no throwable "cause" to be concerned about.
   */
  private Throwable isValidZEvesInclDecl(Expr expr)
  {
    Throwable cause = null;
    if (!(expr instanceof DecorExpr || expr instanceof RenameExpr || expr instanceof RefExpr))
    {
      cause = new UnsupportedAstClassException();
    }
    return cause;
  }

  /**
   * Check whether the given predicate is an AndPred split across multiple lines (i.e. has Op.NL).
   */
  private boolean isNLAndPred(Pred pred)
  {
    return (pred instanceof AndPred && ((AndPred) pred).getAnd().equals(And.NL));
  }

  /**
   * Checks whether the given schema text has empty declarations or not. If it has, then
   * this should be a labelled-predicate or a predicate paragraph rather than an axiomatic/generic box.
   */
  private boolean isPredicatePara(SchText schText)
  {
    return ZUtils.assertZSchText(schText).getZDeclList().isEmpty();
  }

  /**
   * Wraps-up a translated zevesPara within a Z/Eves XML command name "add-paragraph".
   */
  private String wrapPara(String zevesPara)
  {
    final String result = format(ZEVES_COMMAND, "add-paragraph", zevesPara);
    return result;
  }

  // TODO: not being handled here but at Eclipse level because of interactivity
  private String wrapProofCommand(String zevesProof)
  {
    return format(ZEVES_COMMAND, "proof-command", zevesProof);
  }

  private String comment(String headline, String text)
  {
    return format(COMMENT_PATTERN, headline, text);
  }

  /**
   * Retrieves the location string attribute present as a term annotation.
   */
  private String getLocation(Term term)
  {
    /* NOTE:
     *
     * Mark Saaltink said: "Locations are used in the GUI to record the origin of a paragraph (either from a file or from the GUI itself).
     * This is used so that if you re-import a LaTeX file after revising it, the appropriate paragraphs are updated. Just ignore it."
     */
    LocAnn loc = term.getAnn(LocAnn.class);
    return loc == null ? "" : format(LOCATION_PATTERN, loc.getLine(), loc.getCol(), loc.getStart(), loc.getEnd(), loc.getLength(), loc.getLoc());
  }

  /**
   * Returns the string valued result for the current status of the ability flag
   * present as a term annotation.
   */
  private String getAbility(Term term)
  {
    return getAbility(ZEvesUtils.getLabel(term));
  }

  /**
   * Returns the string valued result for the current status of the ability flag
   * present as a term annotation.
   */
  private String getAbility(ZEvesLabel label)
  {
    if (label == null || label.getAbility() == LabelAbility.none)
    {
      return "";
    }

    return format(ABILITY_PATTERN, label.getAbility().name());
  }

  /**
   * Retrieves the usage string attribute present as a term annotation.
   * Usage is only allowed for ConjPara and Pred, where IllegalArgumentException is
   * thrown for other terms.
   */
  private String getUsage(ZEvesLabel label)
  {
    if (label == null || label.getUsage() == LabelUsage.none)
    {
      return "";
    }

    return format(USAGE_PATTERN, label.getUsage().name());
  }

  private String getLabel(Term term)
  {
    ZEvesLabel l = ZEvesUtils.getLabel(term);
    String result = "";
    if (l != null)
    {
      result = format(LABEL_PATTERN,
              l.getAbility().equals(LabelAbility.none) ? "" : l.getAbility().name(),
              l.getUsage().equals(LabelUsage.none) ? "" : l.getUsage().name(),
              getName(l.getName()));
    }
    return result;
  }

  /* Special Z/Eves API Productions */
  /**
   * Methods which implements Section 7 Entities, of the Z/Eves Core API
   */
  private String translateWord(String word)
  {
    if (word.startsWith(ZString.DELTA))
    {
      word = "&Delta;" + word.substring(ZString.DELTA.length());
    }
    else if (word.startsWith(ZString.XI))
    {
      word = "&Xi;" + word.substring(ZString.XI.length());
    }
    else if (word.startsWith(ZString.THETA))
    {
      word = "&theta;" + word.substring(ZString.THETA.length());
    }
    else if (word.equals(ZString.NAT))
    {
      word = "&Nopf;";
    }
    else if (word.equals(ZString.NUM))
    {
      word = "&Zopf;";
    }
    else if (word.equals(ZString.ARITHMOS))
    {
      word = "&Aopf;";
    }
    else if (word.equals(ZString.FINSET))
    {
      word = "&Fopf;";
    }
    else if (word.equals(ZString.POWER))
    {
      word = "&Popf;";
    }
    else if (word.equals(ZString.EMPTYSET))
    {
      word = "&empty;";
    }
    else if (word.equals(ZString.BIGCUP))
    {
      word = "&bigcup;";
    }
    else if (word.equals(ZString.BIGCAP))
    {
      word = "&bigcap;";
    }
    else if (ROMAN_NAMES.contains(word))
    {
      word = format(ROMAN_PATTERN, word);
    }

    return word;
  }

  /**
   * Returns the word part of a DeclName ensuring it is not empty.
   */
  private String getWord(ZName name)
  {
    ZName zname = ZUtils.assertZName(name);
    assert zname != null && zname.getWord().length() > 0 : "A valid word can be neither null nor empty.";
    String result = zname.getWord();
    result = translateWord(result);
    return result;
  }

  private String getSchExprOpName(SchExpr2 term)
  {
    String result;
    if (term instanceof CompExpr)
    {
      result = "&fatsemi;";
    }
    else if (term instanceof PipeExpr)
    {
      result = "&gtgt";
    }
    else if (term instanceof ProjExpr)
    {
      result = "&uharr;";
    }
    else if (term instanceof AndExpr)
    {
      result = "&wedge;";
    }
    else if (term instanceof OrExpr)
    {
      result = "&vee;";
    }
    else if (term instanceof ImpliesExpr)
    {
      result = "&rArr;";
    }
    else if (term instanceof IffExpr)
    {
      result = "&hArr;";
    }
    else
    {
      throw new ZEvesIncompatibleASTException("binary schema expression term", term);
    }
    return result;
  }

  private String getFixity(OperatorName.Fixity fixity)
  {
    String result;
    if (fixity == OperatorName.Fixity.PREFIX)
    {
      result = "pre-rel";
    }
    else if (fixity == OperatorName.Fixity.POSTFIX)
    {
      result = "post-fun";
    }
    else if (fixity == OperatorName.Fixity.INFIX)
    {
      result = "in-rel";
    }
    else // if (fixity == OperatorName.Fixity.NOFIX) or everything else.
    {
      result = "";
    }
    return result;
  }

  private String translateOperatorWord(String word)
  {
    // Strip the ARG_TOK.
    //word = word.substring(word.indexOf(ZString.ARG_TOK)+ZString.ARG_TOK.length(), word.lastIndexOf(ZString.ARG_TOK));
    String result;
    // Sets
    if (word.equals(ZString.NEQ))
    {
      result = "&neq;";
    }
    else if (word.equals(ZString.NOTMEM))
    {
      result = "&notin;";
    }
    // AV: EMPTYSET is not an operator - moving to #translateWord(String)
    //        else if (word.equals(ZString.EMPTYSET))
    //            result = "&empty;";
    // Leo: well spotted ;-)
    else if (word.equals(ZString.SUBSETEQ))
    {
      result = "&subeq;";
    }
    else if (word.equals(ZString.SUBSET))
    {
      result = "&sub;";
    }
    else if (word.equals(ZString.CUP))
    {
      result = "&cup;";
    }
    else if (word.equals(ZString.CAP))
    {
      result = "&cap;";
    }
    else if (word.equals(ZString.SETMINUS))
    {
      result = "\\";
    }
    // Relations
    else if (word.equals(ZString.REL))
    {
      result = "&lrarr;";
    }
    else if (word.equals(ZString.MAPSTO))
    {
      result = "&rtarr;";
    }
    else if (word.equals(ZString.CIRC))
    {
      result = "&circ;";
    }
    else if (word.equals(ZString.DRES))
    {
      result = "&vltri;";
    }
    else if (word.equals(ZString.NDRES))
    {
      result = "&vltrib;";
    }
    else if (word.equals(ZString.RRES))
    {
      result = "&vrtri;";
    }
    else if (word.equals(ZString.NRRES))
    {
      result = "&vrtrib;";
    }
    else if (word.equals(ZString.TILDE))
    {
      result = "&suptilde;";
    }
    else if (word.equals(ZString.LIMG))
    {
      result = "&lvparen;";
    }
    else if (word.equals(ZString.RIMG))
    {
      result = "&rvparen;";
    }
    else if (word.equals(ZString.OPLUS))
    {
      result = "&oplus;";
    }
    else if (word.equals(ZString.COMP))
    {
      result = "&fatsemi;";
    }
    else if (word.equals(ZString.NE + ZString.PLUS + ZString.SW))// % ^+
    {
      result = "&supplus;";
    }
    else if (word.equals(ZString.NE + ZString.MULT + ZString.SW))// % ^*
    {
      result = "&supstar;";
    }
    // Functions
    else if (word.equals(ZString.PFUN))
    {
      result = "&rarrb;";
    }
    else if (word.equals(ZString.FUN))
    {
      result = "&rarr;";
    }
    else if (word.equals(ZString.PINJ))
    {
      result = "&rarrbtl;";
    }
    else if (word.equals(ZString.INJ))
    {
      result = "&rarrtl;";
    }
    else if (word.equals(ZString.PSURJ))
    {
      result = "&Rarrb;";
    }
    else if (word.equals(ZString.SURJ))
    {
      result = "&Rarr;";
    }
    else if (word.equals(ZString.BIJ))
    {
      result = "&Rarrtl;";
    }
    // Natural Numbers
    else if (word.equals(ZString.LESS))
    {
      result = "&lt;";
    }
    else if (word.equals(ZString.LEQ))
    {
      result = "&leq;";
    }
    else if (word.equals(ZString.GREATER))
    {
      result = "&gt;";
    }
    else if (word.equals(ZString.GEQ))
    {
      result = "&geq;";
    }
    else if (word.equals(ZString.FFUN))
    {
      result = "&rarrB;";
    }
    else if (word.equals(ZString.FINJ))
    {
      result = "&rarrBtl;";
    }
    // Sequences
    else if (word.equals(ZString.CAT))
    {
      result = "&frown;";
    }
    else if (word.equals(ZString.EXTRACT))
    {
      result = "&uharl;";
    }
    // POWER can also be used as operator (e.g. P_1), so adding the translation here as well
    else if (word.equals(ZString.POWER))
    {
      result = "&Popf;";
    }
    // An interesting case - FINSET is used as operator name in RefExpr, while
    // for powersets we have PowerExpr. So adding FINSET to operator name translation
    else if (word.equals(ZString.FINSET))
    {
      result = "&Fopf;";
    }
    // for MINUS and NEG, just translate into normal minus
    // Note: from short testing using &neg; crashes Z/Eves sometimes
    else if (word.equals(ZString.MINUS))
    {
      result = "-";
    }
    else if (word.equals(ZString.NEG))
    {
      result = "-";
    }
    else if (word.equals(ZString.LANGLE))
    {
      result = "&lang;";
    }
    else if (word.equals(ZString.RANGLE))
    {
      result = "&rang;";
    }
    else if (ROMAN_NAMES.contains(word))
    {
      result = format(ROMAN_PATTERN, word);
    }
    // Bags
    else if (word.equals(ZEvesString.BCOUNT)) //Bag count
    {
      result = "&sharp;";
    }
    else if (word.equals(ZEvesString.OTIMES))//Bag scaling
    {
        result = "&otimes;";
    }
    else if (word.equals(ZEvesString.INBAG))//Bag membership
    {
      result = "&sqisin;";
    }
    else if (word.equals(ZEvesString.SUBBAGEQ))//sub-bag
    {
      result = "&sqsubeq;";
    }
    else if (word.equals(ZEvesString.UPLUS))//bag union
    {
      result = "&uplus;";
    }
    else if (word.equals(ZEvesString.UMINUS))//bag difference
    {
      result = "&uminus;";
    }
    else if (word.equals(ZString.ARG))
    {
      result = " _ ";
    }
    else if (word.equals(ZString.LISTARG))
    {
      result = " ,, ";
    }
    else
    {
      result = word;
    }
    return result;
  }

  private String adjustIfOpWithinArgument(String s)
  {
    if (s.startsWith(ZString.ARG_TOK) && s.endsWith(ZString.ARG_TOK))
    {
      s = "(" + s + ")";
    }
    return s;
  }

  // ZSchText for AxDef or SchBox should keep args
  private boolean stackTopIsZSchText(Object t)
  {
    return (t instanceof ZSchText);
  }

  // OpNames within DefLHS in Horizontal AxPara
  private boolean stackTopIsOperZName(Object t)
  {
    return ((t instanceof ZName) &&
             ((ZName)t).getOperatorName() != null);
  }

  // ApplExpr with mixfix false should keep opnames
  private boolean stackTopIsExplicitApplExpr(Object t)
  {
    return ((t instanceof ApplExpr) &&
             !((ApplExpr)t).getMixfix().booleanValue());
  }

  // RefExpr with mixfix false that have operator names (e.g., explicitly given RefExpr as "(_op_)")
  // they come from ApplExpr RefExpr with mixfix false or through ApplExpr parameters that might be
  // RefExpr of mixfix false (\_R\_) \comp (\_S \_) say
  private boolean stackTopIsNonMixfixRefExprOper(Object t)
  {
    boolean result =
            ((t instanceof RefExpr) &&
             !((RefExpr)t).getMixfix().booleanValue() &&
             ((RefExpr)t).getZName().getOperatorName() != null);

    if (result)
    {
      result = !stackTopIsRefExprOfApplExprWithExplicitGenActualsNotInfix(t);
    }
    return result;
  }

  // when calling ApplExpr->RefExpr that has explicit generic parameters,
  // ZEves convention is  #[A](S), whereas CZT convention is (# _)[A](S).
  //
  // Now, trouble is for infix operators, the solution is different(!) Nightware...
  // ZEves accepts (_ cup_)[X,Y](A,B). So need to get  special case when ApplExpr.getRightEpr instanceof TupleExpr?
  private boolean stackTopIsRefExprOfApplExprWithExplicitGenActualsNotInfix(Object t)
  {
    boolean result = 
            (fRelationalOpAppl.size() > 1) 
            &&
            ((t instanceof RefExpr) &&
             !((RefExpr)t).getMixfix().booleanValue() &&
             ((RefExpr)t).getExplicit().booleanValue() &&
             ((RefExpr)t).getZName().getOperatorName() != null)
             ;
    if (result)
    {
      Object o = fRelationalOpAppl.elementAt(fRelationalOpAppl.size()-2);
      result = stackTopIsExplicitApplExpr(o);
      if (result)
      {
        result = !(((ApplExpr)o).getRightExpr() instanceof TupleExpr);
      }
    }
    return result;
  }

  // explicit "override" case (e.g., ApplExpr that are not FcnOpAppl - "(_+_)(1,2)"
  private boolean stackTopIsBooleanOverride(Object t)
  {
    return ((t instanceof Boolean) &&
             ((Boolean)t).booleanValue());
  }

  private boolean shouldKeepOpArgsInOpName()
  {
    assert !fRelationalOpAppl.isEmpty();
    Object t= fRelationalOpAppl.peek();
    return (stackTopIsZSchText(t) ||                     
            stackTopIsOperZName(t) ||    
            stackTopIsExplicitApplExpr(t) ||
            stackTopIsNonMixfixRefExprOper(t) ||
            stackTopIsBooleanOverride(t)                
           );
  }

  private String getOperator(OperatorName opname)
  {
    // We are concatenating the result. In almost all cases, one gets "THE" operator involved
    // since we are ignoring ARGs. On ocassional special cases (e.g., LANGLE, LIMG, LBLOT, user defined
    // \\listarg op temp), we need to treat it specially, hence we send the whole load of symbols involved.
    //
    // PS: Z/Eves does not accept \\listarg definition by the user.
    String result = "";

    // If the name is tagged for operator consideration
    if (!fRelationalOpAppl.isEmpty())
    {
      // See revision 3986 in the repository if this fails.
      // I used to use opname.iterator, for what now is getWords().
      Iterator<String> parts = Arrays.asList(opname.getWords()).iterator();//opname.iterator();

      boolean keepArgsOverride = shouldKeepOpArgsInOpName();

      // int found = 0;
      while (parts.hasNext())
      {
        String part = parts.next().toString();
        // ignore the arguments: we will know if it's a list arg from ApplExpr arity.
        if (keepArgsOverride || !part.equals(ZString.ARG) && !part.equals(ZString.LISTARG))
        {
          // found++;
          result += translateOperatorWord(part);
        }
      }
      //if (found != 1)
      //{
      //  throw new ZEvesIncompatibleASTException("Translation of complext operator templates is not yet supported. See throwable cause for details.",
      //          new IllegalArgumentException("We only implement translation of unary or binary operator templates with one \"word\" name only. "
      //                                       + "That is, we support mostly all toolkit operators, such as \"_ < _\", but not more complex templates with more tha one \"word\", "
      //                                       + "such as \"_ || _ @ _ \". Check the newest version readme.txt for compatibility details."));
      //}
    }
    // otherwise, this is an operator appearing in a place where it shouldn't
    else
    {
      throw new ZEvesIncompatibleASTException("Incompatible Std Z operator template for Z/Eves: " + opname);
      //throw new ZEvesIncompatibleASTException("Case yet to be handled: getOperator with " + opname + " that is not a relational op appl");
      //getFixity(opname.getFixity());
    }
    assert !result.isEmpty();
    
    String strokes = getStrokes(opname.getStrokes());
    return result + strokes;
  }

  private String getOperator(Term name)
  {
    return getOperator(ZUtils.assertZName(name).getOperatorName());
  }

  /**
   * Retrieves the Schema name from a DeclName: it is just the getWord()
   * method result, as we do not consider Delta and Xi schemas nor decoration
   * for schema names here.
   * Delta and Xi schemas in CZT are RefExpr. Schema decorations in CZT are
   * DecorExpr (e.g. S_0, S', etc).
   */
  private String getSchName(ZName schName)
  {
    return getWord(schName);
  }

  /**
   * Returns a list of strokes simply concatenated as it appears.
   */
  private String getStrokes(StrokeList strokes)
  {
    ZStrokeList zstrokes = ZUtils.assertZStrokeList(strokes);
    
    StringBuilder result = new StringBuilder("");
    for (Stroke stk : zstrokes)
    {
      result.append(stk.accept(this));
    }
    return result.toString();
  }

  /**
   * Represents the ident production. It extracts the word and the decorations
   * (from strokes) from a given DeclName.
   */
  private String getIdent(ZName name)
  {
    StringBuilder result = new StringBuilder(getWord(name));
    // AV: retrieving ZStrokeList from the name, because ZName can never be
    // cast into ZStrokeList and therefore throws exception
    //
    // Leo: yep
    result.append(getStrokes(name.getZStrokeList()));
    return result.toString();
  }

  /**
   * Represents the decl-name production. It does not yet implement operator templates
   * and just recognises Z/Eves identifiers (e.g. work with decoration).
   */
  private String getName(Name name)
  {

    ZName zname = ZUtils.assertZName(name);

    if (zname.getOperatorName() != null)
    {
      return getOperator(zname);
    }
    else
    {
      return getIdent(zname);
    }
  }

  private String extractSeqElem(Expr e)
  {
    assert e instanceof TupleExpr;
    TupleExpr te = (TupleExpr)e;
    assert te.getZExprList().size() == 2;
    Expr seqElem = te.getZExprList().get(1);
    return getExpr(seqElem);
  }

  private void checkStack(Object o)
  {
    assert !fRelationalOpAppl.isEmpty();
    Object e = fRelationalOpAppl.pop();
    assert e == o || (e instanceof Boolean && e.equals(o));
  }

  private String getRefName(RefExpr term)
  {
    fRelationalOpAppl.push(term);
    final String result = getName(term.getZName());
    checkStack(term);
    return result;
  }

  private String getApplExprPart(ApplExpr term)
  {
    fRelationalOpAppl.push(term);
    // if ApplExpr with mixfix true (e.g., not explicit:  (x+y), get the "_+_" without params)
    // otherwise with mixifix false (e.g., explicit: (_+_)(x,y), get the "_+_" with params)

    // mixfix: left expr is the operator, right expr is a tuple with args
    Expr opExpr = ZUtils.isFcnOpApplExpr(term) ?
      ZUtils.getApplExprRef(term) : term.getLeftExpr();
    final String result = getExpr(opExpr);
    checkStack(term);
    return result;
  }

  /**
   * Returns a comma-separated list of identifiers.
   * It represents ident-list, or event-name-list.
   */
  private String getIdentList(ZNameList term)
  {
    assert term != null;
    if (term.isEmpty())
    {
      throw new IllegalArgumentException("Identifier lists must have at least one declaring name");
    }
    StringBuilder result = new StringBuilder("");
    Iterator<Name> it = term.iterator();
    ZName name = ZUtils.assertZName(it.next());
    result.append(getIdent(name));
    while (it.hasNext())
    {
      result.append(", ");
      name = ZUtils.assertZName(it.next());
      result.append(getIdent(name));
    }
    return result.toString();
  }

  private String getNameList(Iterator<Name> it)
  {
    return getNameList(it, false);
  }

  /**
   * Returns a comma-separated list of decl-name or ref-name (but not mixed).
   * It assumes the list is neither null nor empty. It is used to represent
   * various productions related to names with operators.
   */
  private String getNameList(Iterator<Name> it, boolean asOperators)
  {
    StringBuilder result = new StringBuilder("");
    ZName name = ZUtils.assertZName(it.next());
    result.append(getName(name));
    while (it.hasNext())
    {
      result.append(", ");
      name = ZUtils.assertZName(it.next());

      if (asOperators)
      {
        fRelationalOpAppl.push(name);
      }

      result.append(getName(name));

      if (asOperators)
      {
        checkStack(name);
      }
    }
    return result.toString();
  }

  /**
   * Represents a simplified version of production def-lhs.
   * It just take into account our simplified version of var-name production.
   */
  private String getDefLHS(ZName dname)
  {
    // TODO: Include other forms of def-lhs production.

    OperatorName on = dname.getOperatorName();
    final String result;
    if (on != null)
    {
      fRelationalOpAppl.push(dname);
      // Horizontal op defs need to be parenthesised 
      result = "(" + getOperator(on) + ")";
      
      checkStack(dname);
    }
    else
      result = getVarName(dname);
    return result;
  }

  /**
   * Represents a simplified version of production var-name as just ident.
   * It does not take into account operator names for now, but just
   * decorations.
   */
  private String getVarName(ZName dname)
  {
    // TODO: Include other forms of var-name production.
    return getIdent(dname);
  }

  /**
   * Returns the string corresponding to the generic formals.
   * It extracts the generic formals from a list of DeclName putting
   * together additional brackets. If the list is empty, it simply
   * returns the empty string.
   */
  private String getGenFormals(ZNameList term, boolean addNL)
  {
    assert term != null;
    StringBuilder result = new StringBuilder("");
    if (!term.isEmpty())
    {
      result.append("[");
      result.append(getIdentList(term));
      result.append("]");
      if (addNL) result.append(NL_SEP);
    }
    return result.toString();
  }

  /**
   * Represents the gen-actuals Z/Eves XML production. It calls ExprList visitor and
   * puts its result within square brackets.
   */
  private String getGenActuals(ZExprList term)
  {
    if (term.isEmpty())
    {
      throw new IllegalArgumentException("Invalid expression list for generic actuals");
    }
    StringBuilder result = new StringBuilder("[");
    fZExprListSep = ", ";
    result.append(term.accept(this));
    result.append("]");
    return result.toString();
  }

  /**
   * Retrieve the Z/Eves XML for the given non-null predicate, something the calling
   * method must ensure, otherwise a NullPointerException (or indeed an
   * AssertionError) is thrown. Therefore, it always return some non-empty string.
   */
  private String getPred(Pred pred)
  {
    /* NOTE:
     *
     * As Z/Eves allows AndPred to be split across multiple lines
     * rather than a single predicate, we need to take into account
     * AndPred as a list of Pred. This is taken into consideration at
     * getPred0. This is implemented with a descendent recursive procedure
     * that checks the LHS until reach the base case, where it is processed
     * by getPred0, it includes this result, the NL_SEP, and finally
     * proceeds seemingly with the RHS of AndPred.
     *
     */
    assert pred != null;
    StringBuilder result = new StringBuilder("");
    if (isNLAndPred(pred))
    {
      AndPred ap = (AndPred) pred;
      result.append(getPred(ap.getLeftPred()));
      result.append(NL_SEP);
      result.append(getPred(ap.getRightPred()));
    }
    else
    {
      result.append(getPred0(pred));
    }
    assert !result.toString().equals("");
    return result.toString();
  }

  private String getPred0(Pred pred)
  {
    /* NOTE:
     *
     * Some predicates can have a label annotation.
     * CZT predicates does not have labels, as this is a Z/Eves feature.
     * The top-level interface should allow some sort of naming for
     * available CZT predicates so that we can provide a more compliant
     * translation.
     * Label annotations are checked whenever the flag fCheckForLabelAnnotations
     * is true; labels are ignored otherwise. This accounts for productions
     * axiom-part, labelled-axiom-part, and labelled-predicate.
     */
    assert pred != null;
    StringBuilder result = new StringBuilder("");
    if (fCheckForLabelAnnotations)
    {
      result.append(getLabel(pred));
    }
    String p = pred.accept(this).toString();
    result.append(p);
    return result.toString();
  }

  // e.g., for ApplExpr with mixfix true RefExpr has mixfix false, but shouldn't get operators              (x + y) or (\_R\_) \comp (\_ S\_)
  //       whereas for ApplExpr with mixfix false RefExpr also has mixfix false, but *must* get operators!  (_+_)(x,y) (\_\comp\_)((\_R\_), (\_S\_))
  private boolean isWihtinFcnOpApplExpr(Expr expr)
  {
    return (((expr instanceof RefExpr) &&
            !((RefExpr)expr).getMixfix().booleanValue()) &&
            !fRelationalOpAppl.isEmpty() &&
            (fRelationalOpAppl.peek() instanceof ApplExpr) &&
            ZUtils.isFcnOpApplExpr((ApplExpr)fRelationalOpAppl.peek())
            );
  }

  private boolean isWithinMemPredRefExpr(Expr expr)
  {
    return (((expr instanceof RefExpr) &&
            !((RefExpr)expr).getMixfix().booleanValue()) &&
            !fRelationalOpAppl.isEmpty() &&
            (fRelationalOpAppl.peek() instanceof Boolean) &&
            !((Boolean)fRelationalOpAppl.peek()).booleanValue()
            );
  }


//  private boolean isWithinApplExprRefExpr()
//  {
//    return !fRelationalOpAppl.isEmpty() &&
//            fRelationalOpAppl.peek() instanceof ApplExpr &&
//            ZUtils.isFcnOpApplExpr((ApplExpr)fRelationalOpAppl.peek());
//  }

  /**
   * Retrieve the Z/Eves XML for the given non-null expression, something
   * the calling method must ensure, otherwise a NullPointerException (or
   * indeed an AssertionError) is thrown . Therefore, it always return some non-empty string.
   *
   * Push the expr for the various cases where RefExpr with mixfix false might appear as an operator
   * The only special case then, is if the RefExpr is within an ApplExpr.Mixfix(true) case
   */
  private String getExpr(Expr expr)
  {
    assert expr != null;
    boolean pushExpr = ! (isWihtinFcnOpApplExpr(expr) || isWithinMemPredRefExpr(expr));
    if (pushExpr) fRelationalOpAppl.push(expr);
    final String result = expr.accept(this);
    if (pushExpr) checkStack(expr);
    return result;
  }

  /**
   * Represents the branch production used in free-type.
   * It retrieves the var-name and expression for each branch of a free-type.
   */
  private String getBranch(Branch b)
  {
    String result;
    if (b.getExpr() == null)
    {
      result = getIdent(b.getZName());
    }
    else
    {
      result = format(BRANCH_PATTERN, getVarName(b.getZName()), getExpr(b.getExpr()));
    }
    return result;
  }

  /**
   * Represents the decl-part production. It prefixes the result of visiting the DeclList
   * with the additional XML tag needed by Z/Eves.
   */
  private String getDeclPart(ZDeclList decls)
  {
    StringBuilder result = new StringBuilder("<decl-part/>");
    result.append(decls.accept(this));
    return result.toString();
  }

  /**
   * Retrives the axiomatic part of schemas, axiomatic and generic boxes.
   * If the predicate is null, it simply returns the empty string.
   * Otherwise, appropriate Z/Eves XML tags are added.
   */
  private String getAxiomPart(Pred pred)
  {
    StringBuilder result = new StringBuilder("");
    if (pred != null)
    {
      result.append("<ax-part/>");
      result.append(getPred(pred));
    }
    return result.toString();
  }

  /**
   * Proof part of a theorem-def production. It extracts proof commands from a
   * Proof annotation within ConjPara.
   *
   */
  private String getProofPart(ConjPara term)
  {
	  // We do not support inline proof commands at the moment, so proof script
	  // is a separate AST element and is sent to Z/Eves separately
//    StringBuilder result = new StringBuilder("");
//    //ProofScript ps = ProofUtils.getProofScriptAnn(term);
//    String ps = "";
//    if (ps != null)
//    {
//      result.append("<proof-part/>");
//      result.append(ps);
//    }
//    return result.toString();
	  return "";
  }

  /**
   * Returns the internal Z/Eves quantifier name according to the corresponding CZT QntPred subclass.
   */
  private String getQntName(QntPred term)
  {
    if (term instanceof ExistsPred)
    {
      return "&exists; ";
    }
    else if (term instanceof Exists1Pred)
    {
      return "&exists;&sub1; ";
    }
    else if (term instanceof ForallPred)
    {
      return "&forall; ";
    }
    else
    {
      throw new ZEvesIncompatibleASTException("Quantified predicate", term);
    }
  }

  /**
   * Returns the internal Z/Eves quantifier name according to the corresponding CZT QntExpr subclass.
   */
  private String getQntName(QntExpr term)
  {
    if (term instanceof ExistsExpr)
    {
      return "&exists; ";
    }
    else if (term instanceof Exists1Expr)
    {
      return "&exists;&sub1; ";
    }
    else if (term instanceof ForallExpr)
    {
      return "&forall; ";
    }
    else
    {
      throw new ZEvesIncompatibleASTException("Quantified expression", term);
    }
  }

  /**
   * Returns the internal Z/Eves predicate name according to the corresponding CZT Pred2 subclass.
   */
  private String getBinPredName(Pred2 term)
  {
    String result;
    if (term instanceof IffPred)
    {
      result = "&hArr;";
    }
    else if (term instanceof ImpliesPred)
    {
      result = "&rArr;";
    }
    else if (term instanceof OrPred)
    {
      result = "&vee;";
    }
    else if (term instanceof AndPred)
    {
      And op = ((AndPred) term).getAnd();
      if (op.equals(And.Wedge) || op.equals(And.Chain))
      {
        result = "&wedge;";
      }
      else if (op.equals(And.NL))
      {
        throw new ZEvesIncompatibleASTException("AndPred with new line cannot be converted through predicate tree visiting. "
                                                + "NL AndPred can only appear through the axiom-part production.");
      }
      else
      {
        throw new ZEvesIncompatibleASTException("Chain and Semi AndPred appearing in the predicate tree visiting has not yet been implemented."
                                                + "Chain AndPred appears with predicates such as \"x = y = z\", which can be easily avoided.");
      }
    }
    else
    {
      throw new ZEvesIncompatibleASTException("Quantified predicate", term);
    }
    return result;
  }

  /**
   * Retrieves the kind of the given MemPred.
   * It deals with the four cases available for: set containment (ex: X isin Y),
   * n-ary and unary relational operator application (X < Y, disjoint~S), and
   * equality (X = Y). It throws a ZEvesIncompatibleASTException when none
   * of these cases can be identified.
   */
  private MemPredKind getMemPredKind(MemPred term)
  {
    /* NOTE (from CZT Z.xsd file):
     *
     * A relation operator application (C.5.12).
     * The mixfix attribute is false iff the input has the form Expr1 in Expr2.
     * When mixfix=true, the second (right) Expr must be either a
     * relational operator and the first (left) Expr must be a tuple
     * containing the corresponding number of arguments (unless the
     * operator has one argument, then no tuple is required) or an
     * equality and the the second (right) Expr must be a set expression
     * containing exactly one expression.
     * For example, the input "m &lt; n" generates a MemPred element with
     * mixfix=true, left=(m,n) and right=" _ &lt; _ ", whereas
     * "(m,n) in (_ &lt; _)" has the same left and right expressions,
     * but mixfix=false.
     *
     */
    /* NOTE (MemPred cases):
     *
     * case1: mixfix=false ex: E1 in E2
     *      Left  = any expr
     *      Right = any expr
     *
     * case2: mixfix=true
     *
     * case2.1: Relational operator application
     *      case2.1.1: More than one argument: ex X subseteq Y
     *          Left  = TupleExpr(RefExpr(X, false), RefExpr(Y,false)) &
     *          Right = RefExpr("_subseteq_", false) (n-ary relOps).
     *
     *      case2.1.2: One argument exactly: ex disjoint X
     *          Left  = Any expr. ex: SetExpr, RefExpr(X, false), etc...
     *          Right = RefExpr("disjoint_", false)! (unary relOps).
     *
     * case2.2: Equality  x = y
     *      Left  = RefExpr(x, false)
     *      Right = SetExpr(RefExpr(y, false))
     *
     */
    MemPredKind result;
    if (!term.getMixfix())
    { // case 1
      result = MemPredKind.SET_MEMBERSHIP;
    }
    else
    {
      Expr right = term.getRightExpr();
      if (right instanceof RefExpr)
      {        // case 2.1
        Expr left = term.getLeftExpr();
        if (left instanceof TupleExpr) // case 2.1.1
        {
          result = MemPredKind.NARY_RELOP_APPLICATION;
        }
        else // case 2.1.2
        {
          result = MemPredKind.UNARY_RELOP_APPLICATION;
        }
      }
      else if (right instanceof SetExpr)
      { // case 2.2
        result = MemPredKind.EQUALITY;
      }
      else
      {
        throw new ZEvesIncompatibleASTException("Invalid relational operator application, while trying to convert"
                                                + "CZT membership predicate to Z/Eves XML API. See throwable cause for details.",
                new IllegalArgumentException("In CZT (and Z standard) relational operators can appear as predicates. "
                                             + "There are two cases to consider: n-ary, and unary relational operators. For n-ary operators, the "
                                             + "left expression must be a TupleExpr containing all the arguments for the relational operator. For "
                                             + "instance, x~\\subseteq~y is represented as (mixfix=boolean values) \n\t "
                                             + "MemPred(TupleExpr(RefExpr(\"x\", false), RefExpr(\"y\", false)), RefExpr(\"_~\\subseteq~_\", false), true)\n "
                                             + "On ther other hand, for unary operators, the left expression can be the actual expression being applied"
                                             + "for the relational operator in question. For instance, \\disjoint~{ s, t } is represeted as \n\t "
                                             + "MemPred(SetExpr(RefExpr(\"s\", false), RefExpr(\"t\", false)), RefExpr(\"\\disjoint~_\"), true)"));
      }
    }
    return result;
  }

  /**
   * Returns the relational operator name for the given RefExpr, which is part of a MemPred term.
   */
  private String getMemPredRelOpName(RefExpr refExpr)
  {
    // for MemPred, we need to treat the RefExpr differently: don't push it because it is always mixfix=false
    //fRelationalOpAppl.push(refExpr);
    fRelationalOpAppl.push(refExpr.getMixfix());
    String result = getExpr(refExpr);

    checkStack(refExpr.getMixfix());

    if (result == null || result.equals(""))
    {
      throw new ZEvesIncompatibleASTException("Relational operator could not be translated. See throwable cause for details.",
              new IllegalArgumentException("It wasn't possible to properly translate relational operator "
                                           + refExpr.getZName().toString() + " into Z/Eves format."));
    }
    return result;
  }

  /* Top-level operations */
  public String print(Term term, SectionInfo si)
  {
    setSectionInfo(si);
    return print(term);
  }

  /**
   * Top-level method which translates the given CZT term to a corresponding Z/Eves
   * server XML API. It only accepts Para, Pred, or Expr because Z/Eves adds sections
   * via a set of commands rather than a simple command.
   * @param term
   * @return
   */
  public String print(Term term)
  {
    if (term == null)
    {
      throw new NullPointerException("Cannot convert a null term to Z/Eves XML");
    }
    if (!(term instanceof Para || term instanceof Pred || term instanceof Expr
          || term instanceof ZName))
    {
      throw new ZEvesIncompatibleASTException("This class can only print Names, Para, Pred, and Expr terms. For other "
                                              + "terms such as Spec and ZSection, one should use the ZEvesEvaluator class, as it allows appropriate "
                                              + "handling of Z sections through special commands needed by the Z/Eves server.");
    }
    return term.accept(this);
  }

  public List<String> printSpec(Spec term, SectionInfo si)
  {
    setSectionInfo(si);
    return printSpec(term);
  }

  public List<String> printSpec(Spec term)
  {
    return term.accept(fSpecPrinter);
  }

  public List<String> printZSect(ZSect term, SectionInfo si)
  {
    setSectionInfo(si);
    return printZSect(term);
  }

  public List<String> printZSect(ZSect term)
  {
    return term.accept(fSpecPrinter);
  }

  public final void setSectionInfo(SectionInfo si)
  {
    fSectionInfo = si;
  }

  public SectionInfo getSectionInfo()
  {
    return fSectionInfo;
  }
  
  public final void setSectionName(String sectionName) {
    this.fSectionName = sectionName;
  }

  /* Special Terms */
  @Override
  public String visitTerm(Term term)
  {
    throw new ZEvesIncompatibleASTException("Term", term);
  }

  @Override
  public String visitFreetype(Freetype term)
  {
    if (ZUtils.assertZBranchList(term.getBranchList()).isEmpty())
    {
      throw new IllegalArgumentException("Free type declarations must have at least one branch.");
    }
    StringBuilder result = new StringBuilder(getIdent(term.getZName()));
    result.append("::=");
    Iterator<Branch> it = ZUtils.assertZBranchList(term.getBranchList()).iterator();
    Branch b = it.next();
    result.append(getBranch(b));
    while (it.hasNext())
    {
      result.append(" | ");
      b = it.next();
      result.append(getBranch(b));
    }

    // AV: Freetype is not a paragraph, and will get an exception in Location and Ability, therefore ignore them.
    //return format(ZED_BOX_FREETYPE_PATTERN, "", "", result.toString());

    // Leo: new parser considers this and each free type is assumed to have the ability of the top-most \begin{zed} enclosing it.
    return format(ZED_BOX_FREETYPE_PATTERN, getLocation(term), getAbility(term), result.toString());

    // Leo: FreePara needs to handle Loc/Ability, but in Z/Eves the ability is placed on the
    //      the top of a Z-box (e.g., \begin[disabled]{zed}, and not at the individual boxed para).
    // TODO: think about a solution to this for later.
  }

  @Override
  public String visitSchText(SchText termx)
  {
    ZSchText term = ZUtils.assertZSchText(termx);
    StringBuilder result = new StringBuilder("");
    boolean needBar = false;
    if (!term.getZDeclList().isEmpty())
    {
      result.append(term.getZDeclList().accept(this));
      needBar = true;
    }
    if (term.getPred() != null)
    {
      if (needBar)
      {
        result.append(" | ");
      }
      result.append(getPred(term.getPred()));
    }
    return result.toString();
  }

  @Override
  public String visitZName(ZName term)
  {
    return getName(term);
  }

  /* Special Z Lists */
  /**
   * Represents the declaration production. Firstly, it checks for empty
   * declaration incompatibility. Next, it iterates through all elements from the
   * list appending the definition for each Decl from decls.
   * @param decls
   */
  @Override
  public String visitZDeclList(ZDeclList decls)
  {

    /* NOTE:
     *
     * Z/Eves does not accept empty declarations, as allowed by the Z standard.
     * Therefore, we do need to restrict the CZT here with and additional check.
     */
    if (decls.isEmpty())
    {
      emptyDeclPartException();
    }
    StringBuilder result = new StringBuilder("");
    Iterator<Decl> it = decls.iterator();
    Decl d = it.next();
    result.append(d.accept(this));
    while (it.hasNext())
    {
      // Using semicolon for all declaration lists, because Z/Eves expects
      // semicolons in horizontal definitions, theorems, etc.
      result.append(SC_SEP);
      d = it.next();
      result.append(d.accept(this));
    }
    return result.toString();
  }

  /**
   * Represents the expression-list production. It ensures first that the list
   * is not empty, and then traverse it by building up a comma-separated list
   * of expressions.
   */
  @Override
  public String visitZExprList(ZExprList term)
  {
    assert !term.isEmpty() && fZExprListSep != null
           && !fZExprListSep.equals("") : "Expression list can be neither null nor empty.";
    StringBuilder result = new StringBuilder("");
    Iterator<Expr> it = term.iterator();
    Expr e = it.next();
    // for when ZExprList contains RefExpr that are operators ans hace mixfix false
    // e.g.,  (\_R\_, \_S\_) \in (\_ \subseqeq \_) (!)
    fRelationalOpAppl.push(e);
    String resp = getExpr(e);
    resp = adjustIfOpWithinArgument(resp);
    result.append(resp);
    checkStack(e);
    while (it.hasNext())
    {
      result.append(fZExprListSep);
      e = it.next();
      fRelationalOpAppl.push(e);
      resp = getExpr(e);
      resp = adjustIfOpWithinArgument(resp);
      result.append(resp);
      checkStack(e);
    }
    return result.toString();
  }

  @Override
  public String visitZNameList(ZNameList term)
  {
    return getNameList(term.iterator());
  }

  /* Z Strokes */
  /* NOTE:
   *
   * Z/Eves strokes are just plain text. They do not have the special
   * Z Standard symbols such as ZString.SE + ZString.NW.
   *
   */
  @Override
  public String visitStroke(Stroke term)
  {
    throw new ZEvesIncompatibleASTException("Stroke", term);
  }

  @Override
  public String visitNumStroke(NumStroke term)
  {
    Integer i = term.getDigit().getValue();
    if (i < 0 || i > 9)
    {
      throw new ZEvesIncompatibleASTException("Z/Eves only accepts number strokes from 0 up to 9 (inclusive)");
    }
    return format(NUM_STROKE_PATTERN, i.toString());
  }

  @Override
  public String visitInStroke(InStroke term)
  {
    return "?";
  }

  @Override
  public String visitOutStroke(OutStroke term)
  {
    return "!";
  }

  @Override
  public String visitNextStroke(NextStroke term)
  {
    return "&apos;";
  }

  /* Z Paragraphs */
  @Override
  public String visitPara(Para term)
  {
    throw new ZEvesIncompatibleASTException("Paragraph", term);
  }

  @Override
  public String visitNarrPara(NarrPara term)
  {
    return comment("Narrative Paragraph", term.getContent().toString());
  }

  @Override
  public String visitLatexMarkupPara(LatexMarkupPara term)
  {
    return comment("LaTeX Markup Directives Paragraph", term.getDirective().toString());
  }

  @Override
  public String visitUnparsedPara(UnparsedPara term)
  {
    return comment("Unparsed Paragraph", term.getContent().toString());
  }

  @Override
  public String visitOptempPara(OptempPara term)
  {
    Assoc a = term.getAssoc();
    BigInteger p = term.getPrec();
    int prec = 0;
    if (p != null) prec = p.intValue();
    Cat cat = term.getCat();
    String operator = null;
    String opClass = null;
    int place = 1;
    Iterator<Oper> it = term.getOper().iterator();
    List<Integer> opClassIdxs = new ArrayList<Integer>();
    StringBuilder opsComment = new StringBuilder();
    while (it.hasNext())
    {
      Oper op = it.next();
      if (op instanceof Operator)
      {
        if (operator != null)
          throw new ZEvesIncompatibleASTException("ZEves does not allow multiple-word operators; relational image is predefined.");
        operator = ((Operator)op).getWord();
        opsComment.append(operator);
      }
      else if (op instanceof Operand)
      {
        if (((Operand)op).getList())
          throw new ZEvesIncompatibleASTException("ZEves does not allow list-arg operators; sequence display is predefined.");
        else
        {
          opClassIdxs.add(place);
          opsComment.append(ZString.ARG_TOK);
        }
      }
      place++;
    }
    if (opClassIdxs.size() == 2)
    {
      // infix
      switch (cat)
      {
        case Function:
          assert prec >= 0;
          opClass = "infun" + (prec <= 10 ? "1" : prec <= 20 ? "2" : prec <= 30 ? "3" : prec <= 40 ? "4" : prec <= 50 ? "5" : "6");
          break;
        case Generic:
          opClass = "ingen";
          break;
        case Relation:
          opClass = "inrel";
          break;
      }
    }
    else if (opClassIdxs.size() == 1)
    {
      if (opClassIdxs.get(0) > 1)
      {
        // prefix
        switch (cat)
        {
          case Function:
            throw new ZEvesIncompatibleASTException("ZEves does not allow prefix function operator templates.");
          case Generic:
            opClass = "pregen";
            break;
          case Relation:
            opClass = "prerel";
            break;
        }
      }
      else
      {
        // postfix
        switch (cat)
        {
          case Function:
            opClass = "postfun";
            break;
          case Generic:
          case Relation:
            throw new ZEvesIncompatibleASTException("ZEves only allows postfix function operator templates.");
        }
      }
    }
    else
    {
      // wrong? word? irnore?
      //throw new ZEvesIncompatibleASTException();
      CztLogger.getLogger(getClass()).warning("Could not determine operator fixture for " + operator + ". Assuming 'ignore'");
      opClass = "ignore";
    }
    final String comment = comment("Original operator template",
            format(OPERATOR_TEMPLATE_COMMENT, cat, prec, a, opsComment.toString()));
    final String result = wrapPara(format(OEPRATOR_TEMPLATE_PATTERN, operator, opClass));
    return comment + result;
  }

  @Override
  public String visitConjPara(ConjPara term)
  {
    String axiomPart = getAxiomPart(term.getPred());
    if (axiomPart.equals(""))
    {
      throw new ZEvesIncompatibleASTException("Z/Eves conjectures must not have an empty predicate part.");
    }

    ZEvesLabel l = ZEvesUtils.getLabel(term);
    if (l == null)
    {
      l = ZEvesUtils.addDefaultZEvesLabelTo(term);
    }
    
    final String lName = getName(l.getName());

    if (term.getName() == null)
    {
      term.getAnns().add(ZEvesUtils.FACTORY.createZName(l.getZName()));
    }
    else if (!lName.equals(term.getName()))
    {
      // trust the label more than the "anns" name?
      CztLogger.getLogger(getClass()).warning("Theorem name mismatch: name " + term.getName() + " given, yet label/proof-script name " + lName + " was found. Using the latter.");
      for(Object o : term.getAnns())
      {
        // update the zname for the label name
        if (o instanceof ZName)
        {
          ZName zn = (ZName)o;
          zn.setWord(lName);
          break;
        }
      }
    }
    // use label name for proof and theorem definition
    String result = format(THEOREM_DEF_PATTERN, getLocation(term), getAbility(l), getUsage(l),
            lName, NL_SEP + getGenFormals(term.getZNameList(), true),
            axiomPart, getProofPart(term));
    return wrapPara(result);
  }

  @Override
  public String visitGivenPara(GivenPara term)
  {
    String result = format(ZED_BOX_GIVENSET_PATTERN,
            getLocation(term), getAbility(term), getIdentList(term.getZNameList()));
    return wrapPara(result);
  }

  @Override
  public String visitAxPara(AxPara term)
  {
    /*
     * ADDITIONAL COMMENTS
     * -------------------
     *
     * In CZT, abbreviations, axiomatic and generic definitions,
     * schemas and generic schemas, are all regarded as AxPara.
     * To differentiate Schemas from these one needs to do the following:
     *
     * Schema or generic schema definition (vertical).
     *      AxPara.Box          = SchBox
     *      AxPara.decl         = generics
     *      AxPara.SchText.decl = ConstDecl
     *      AxPara.SchText.pred = null
     *      ConstDecl.dname     = SchemaName
     *      ConstDecl.expr      = SchExpr
     *
     * Axiomatic or generic definitions
     *      AxPara.Box          = AxBox
     *      AxPara.decl         = generics
     *      AxPara.SchText.decl = declared variables
     *      AxPara.SchText.pred = axiomatic predicate
     *
     * Horizontal definition
     *      AxPara.Box          = OmitBox
     *      AxPara.decl         = generics
     *      AxPara.SchText.decl = Constdecl
     *      AxPara.SchText.pred = null
     *      ConstDecl.dname     = HorizDefName (either SchName or AbbrvName)
     *      ConstDecl.expr      = HorizDefExpr (either SchExpr or Other)
     *
     *      So, horizontal definitions with a SchExpr are schemas.
     */
    String result;
    Box b = term.getBox();
    String genFormals = getGenFormals(term.getZNameList(), !b.equals(Box.OmitBox));
    assert genFormals != null;
    if (b.equals(Box.SchBox))
    {
      assert term.getZSchText().getPred() == null;
      ConstDecl cd = (ConstDecl) term.getZSchText().getZDeclList().get(0);
      ZName schName = cd.getZName();
      ZSchText schText = ((SchExpr) cd.getExpr()).getZSchText();

      /* NOTE:
       *
       * Z/Eves does not have a uniform pattern for SchText.
       * In schema-box is appears divided with additional tags as in
       * "<decl-part/> decls and <ax-part/> preds", whereas in a predicates
       * it appears directly as "decls | preds".
       * Therefore, we need to visit specific parts of SchText adding necessary
       * tags for SchBoxes rather than visiting the whole SchText altogether.
       *
       * Moreover, predicate paragraphss can be included whenever the declaration
       * part is empty. We use such "PredPara" for convenience when managing terms
       * (e.g., Expr / Pred) on the fly as para.
       */
      String decls = "";
      String preds = getAxiomPart(schText.getPred());
      if (!isPredicatePara(schText))
      {
        // handle relational operators with appropriate fixity (E.g., x+y instead of (_+_)(x,y))
        fRelationalOpAppl.push(schText);
        // for declared names, keep the operators (e.g., print full op names (_+_):T instead of + only).
        //fKeepOpArgs = true; Just check for schText on the stack
        decls = getDeclPart(schText.getZDeclList());
        //fKeepOpArgs = false;
        checkStack(schText);
        result = format(SCHEMA_BOX_PATTERN, getLocation(term),
                getAbility(term), getSchName(schName), NL_SEP + genFormals, decls, preds);
      }
      else
      {
        if (preds == null || preds.equals(""))
        {
          throw new ZEvesIncompatibleASTException("Schema boxes without declaration must have the predicate part to be considered a Z/Eves predicate paragraph.");
        }
        result = format(PREDICATE_PARA_PATTERN, getLocation(term), getAbility(term), preds);
      }
    }
    else if (b.equals(Box.AxBox))
    {
      /* NOTE:
       *
       * According to Mark Saaltink,  "Standard Z syntax seems to have dropped the predicate paragraph; if I remember
       * correctly, they are replaced by axiom boxes with empty declaration parts. You might use labelled-predicates
       * for these paragraphs, in cases where the user has been able to attach a name to the predicate part."
       *
       * So I will treat CZT empty axiomatic/generic boxes as labelled-predicate producation.
       */
      String decls = "";
      ZSchText schText = term.getZSchText();
      fCheckForLabelAnnotations = true;
      String preds = getAxiomPart(schText.getPred());
      fCheckForLabelAnnotations = false;
      if (!isPredicatePara(schText))
      {
        fRelationalOpAppl.push(schText);
        //fKeepOpArgs = true;
        decls = getDeclPart(schText.getZDeclList());
        //fKeepOpArgs = false;
        checkStack(schText);
        
        if (genFormals.equals(""))
        {
          result = format(AXIOMATIC_BOX_PATTERN,
                  getLocation(term), getAbility(term), decls, preds);
        }
        else
        {
          result = format(GENERIC_BOX_PATTERN, getLocation(term), getAbility(term), genFormals, decls, preds);
        }
      }
      else
      {
        if (preds == null || preds.equals(""))
        {
          throw new ZEvesIncompatibleASTException("Axiomatic boxes without declaration must have the predicate part to be considered a Z/Eves predicate paragraph.");
        }
        result = format(PREDICATE_PARA_PATTERN, getLocation(term), getAbility(term), preds);
      }
    }
    else if (b.equals(Box.OmitBox))
    {
      assert term.getZSchText().getPred() == null;
      ConstDecl cd = (ConstDecl) term.getZSchText().getZDeclList().get(0);
      ZName hdefName = cd.getZName();
      Expr expr = cd.getExpr();
      // We check whether the expression is schema-based to determine if we need the &eqhat; symbol.
      // First we check whether RHS is schema expression, otherwise ask for type information
      boolean isSchExpr = expr instanceof SchExpr || expr instanceof SchExpr2
          || isSchemaTyped(fSectionName, hdefName);
      String zboxItemName = isSchExpr ? getSchName(hdefName) : getDefLHS(hdefName);
      String zboxItemSymbol = isSchExpr ? "&eqhat;" : "==";
      String zboxItemExpr = getExpr(expr);
      result = format(ZED_BOX_HORIZONTAL_PATTERN, getLocation(term), getAbility(term), zboxItemName,
              genFormals, zboxItemSymbol, zboxItemExpr);
    }
    else
    {
      throw new IllegalArgumentException("Invalid box parameter for AxPara");
    }
    return wrapPara(result);
  }

  @Override
  public String visitFreePara(FreePara term)
  {
    /* NOTE 1:
     *
     * Z/Eves does not have free-type paragraphs with more than one freetype
     * declaration, as allowed by the Z Standard with the & character.
     * To allow compliance with CZT parsed elements, we just accept it by
     * expanding then into individual FreeType definitions in Z/Eves.
     *
     * TODO: Ask Mark Utting/Ian Toyn if this creates a problem. For instance,
     *       can one make reference to previous free types in such in-line
     *       definition?
     */
    StringBuilder result = new StringBuilder("");
    for (Freetype ft : ZUtils.assertZFreetypeList(term.getFreetypeList()))
    {
      /* NOTE 2:
       *
       * Thus, we wrap each individual freetype paragraph (ZED_BOX)
       * as an "add-paragraph" ZEVES_COMMAND!
       */
      result.append(wrapPara(ft.accept(this).toString()));
    }
    return result.toString();
  }

  /* Declarations */
  @Override
  public String visitDecl(Decl term)
  {
    throw new ZEvesIncompatibleASTException("Declaration", term);
  }

  @Override
  public String visitInclDecl(InclDecl term)
  {
    /* NOTE:
     *
     * Z/Eves only allows inclusion of schema-ref, rather than the general
     * schema-expr allowed by the Z Standard (and CZT).
     * Therefore, we can only accept here RefExpr, which represent schema
     * references, including Delta and Xi schemas. We must also accept
     * DecorExpr, as Z/Eves considers this to be schema-ref as well.
     *
     * A tricky issue is that Z/Eves allows schema replacements or CZT
     * RenameExpr as an additional kind of schema-ref. This case must also
     * be dealt with here. Furthermore, Z/Eves also allows nonstandard
     * schema updates with a kind of assignment operation. This needs to
     * be taken into account, perhaps separetely as term annotations.
     *
     * In summary, we MUST ONLY treat the following expression types from
     * inclusion declarations:
     *
     * 1) DecorExpr     => for decoration such as S' or S_0
     * 2) RenameExpr    => for replacements such as S[x/y] or special kind S[x := y] with annotation.
     * 3) RefExpr       => for a RefName or to any of the two above.
     *
     * Every other case MUST throw an incompatibility exception.
     */
    Throwable cause = isValidZEvesInclDecl(term.getExpr());
    if (cause != null)
    {
      throw new ZEvesIncompatibleASTException("Z/Eves restricts the kinds of expressions that can be used "
                                              + "in inclusion declarations. The expression present on the current inclusion could not be "
                                              + "translated. Please look at the throwable cause for further details.", cause);
    }

    return getExpr(term.getExpr());
    //return "";
  }

  /* NOTE:
   *
   * CZT ConstDecl cannot appear for Z/Eves.
   * In CZT It only appears during definition of paragraphs, which are
   * treated specially and separetely without visiting ConstDecl.
   * Therefore, we leave it to be caught by the generic Decl as an error.
   *
  @Override public String visitConstDecl(ConstDecl term) {
  return term;
  }
   */
  @Override
  public String visitVarDecl(VarDecl term)
  {
    if (term.getZNameList().isEmpty())
    {
      throw new IllegalArgumentException("Empty basic declaration list (at CZT VarDecl) is not allowed.");
    }
    if (term.getExpr() == null)
    {
      throw new IllegalArgumentException("Empty basic declaration expression (at CZT VarDecl) is not allowed.");
    }
    /* NOTE:
     *
     * This visitor represent parts of basic-decl, precisely,
     * decl-name-list : expr
     */
    StringBuilder result = new StringBuilder(getNameList(term.getZNameList().iterator()));
    result.append(": ");
    result.append(getExpr(term.getExpr()));
    return result.toString();
  }

  /* Z Predicates */
  @Override
  public String visitPred(Pred term)
  {
    throw new ZEvesIncompatibleASTException("Predicate", term);
  }

  @Override
  public String visitTruePred(TruePred term)
  {
    return "true";
  }

  @Override
  public String visitFalsePred(FalsePred term)
  {
    return "false";
  }

  @Override
  public String visitNegPred(NegPred term)
  {
    return format(NEG_PRED_PATTERN, getPred(term.getPred()));
  }

  @Override
  public String visitQntPred(QntPred term)
  {
    /* NOTE: This case covers quatifiers Exists, Exists1, and Forall.
     */


    // we could have operator templates within these schText classes.
    ZSchText schText = term.getZSchText();
    fRelationalOpAppl.push(schText);
    final String schTextPart = schText.accept(this);
    checkStack(schText);
    
    return format(QNT_PRED_PATTERN, getQntName(term), schTextPart, getPred(term.getPred()));
  }

  @Override
  public String visitPred2(Pred2 term)
  {
    /* NOTE: This case covers predicates iff, implies, and, or.
     */
    return format(BIN_PRED_PATTERN, getPred(term.getLeftPred()), getBinPredName(term), getPred(term.getRightPred()));
  }

  @Override
  public String visitMemPred(MemPred term)
  {
    /* NOTE: This case covers isin, and relational operators (n-ary, unary, and =).
     */
    /*
     * A relation operator application (C.5.12).
     *   <ul>
     *   <li>Membership predicate.
     *       In this case, Mixfix=false, the first (left) expression is the
     *       element, and the second (right) expression is the set.
     *       For example, "n \in S" has left="n" and right="S".</li>
     *   <li>Equality.
     *       In this case, Mixfix=true, the first (left) expression is the
     *       left-hand side of the equality, and the second (right)
     *       expression is a singleton set containing the right-hand side
     *       of the equality.
     *       For example: "n = m" has left="n" and right="{m}".</li>
     *   <li>Other operator application.
     *       In this case, Mixfix=true, the first (left) expression is
     *       usually a tuple containing the corresponding number of arguments,
     *       and the second (right) expression is the operator name.
     *       However, for a unary operator, the left expression does not have
     *       to be a tuple.
     *       For example, "n &lt; m" has left="(n,m)" and right=" _ &lt; _ ",
     *       "disjoint s" has left="s" and right="disjoint _ ", and
     *       if foo was declared as a unary postfix operator,
     *       then "(2,3) foo" would have left= "(2,3)" and right=" _ foo".
     *       </li>
     */
    MemPredKind kind = getMemPredKind(term);
    String rel, left, right;
    Expr lhs, rhs;
    switch (kind)
    {
      // for the various cases, push expressions to the op-treatment stack. If it's a refExpr with mixfix false, it will get op ARG_TOK
      case SET_MEMBERSHIP:
        lhs = term.getLeftExpr();
        rhs = term.getRightExpr();
        fRelationalOpAppl.push(lhs);
        left = getExpr(lhs);
        checkStack(lhs);
        rel = "&isin;";
        fRelationalOpAppl.push(rhs);
        right = getExpr(rhs);
        checkStack(rhs);
        break;
      case NARY_RELOP_APPLICATION:
        ZExprList params = ((TupleExpr) term.getLeftExpr()).getZExprList();
        assert !params.isEmpty();
        if (params.size() != 2)
        {
          throw new ZEvesIncompatibleASTException("Current version only supports translation of binary relational operators.");
        }
        lhs = params.get(0);
        rhs = params.get(1);
        fRelationalOpAppl.push(lhs);
        left = getExpr(lhs);
        checkStack(lhs);
        rel = getMemPredRelOpName((RefExpr) term.getRightExpr());
        fRelationalOpAppl.push(rhs);
        right = getExpr(rhs);
        checkStack(rhs);
        break;
      case UNARY_RELOP_APPLICATION:
        RefExpr refexpr = (RefExpr) term.getRightExpr();
        OperatorName.Fixity fixity = refexpr.getZName().getOperatorName().getFixity();
        rel = getMemPredRelOpName(refexpr);
        /* NOTE:
         * The actual unary parameter comes from the left expression and is placed according to the fixture.
         */
        lhs = term.getLeftExpr();
        fRelationalOpAppl.push(lhs);
        if (fixity == OperatorName.Fixity.PREFIX)
        {
          // Prefix: left+rel+right = ""+rel+right
          left = "";
          right = getExpr(lhs);
        }
        else if (fixity == OperatorName.Fixity.POSTFIX)
        {
          // Postfix: left+rel+right = left+rel+""
          left = getExpr(lhs);
          right = "";
        }
        else
        {
          throw new ZEvesIncompatibleASTException("Unsupported fixture for relational operator (" + fixity.toString() + ").");
        }
        checkStack(lhs);
        break;
      case EQUALITY:
        /* NOTE:
         *
         * For equality, the left expression is a Expr, whereas the
         * right expression must be a SetExpr containing only one element
         */
        lhs = term.getLeftExpr();
        rhs = ((SetExpr) term.getRightExpr()).getZExprList().get(0);
        fRelationalOpAppl.push(lhs);
        left = getExpr(lhs);
        checkStack(lhs);
        rel = " = ";
        fRelationalOpAppl.push(rhs);
        right = getExpr(rhs);
        checkStack(rhs);
        break;
      default:
        throw new AssertionError("Invalid MemPredKind " + kind);
    }
    left = adjustIfOpWithinArgument(left);
    right = adjustIfOpWithinArgument(right);
    String result = format(MEMPRED_PATTERN, left, rel, right);
    assert result != null && !result.equals("");
    return result;
  }

  @Override
  public String visitExprPred(ExprPred term)
  {
    /* NOTE: This case covers schema-ref, refexpr, schema precondition, conditional, and let.
     */
    return getExpr(term.getExpr());
  }

  /* NOTE: Dealt with directly through visitPred2. The case with NL is not
   *       allowed here. It can only appear for axiom-part instead, and is
   *       dealt with by getAxiomPart directly. The need for this is due to
   *       our design decision to include labelled-predicate whilst translating.
   *
  @Override public String visitAndPred(AndPred term) {
  }
   */
  /* Z Expressions */
  @Override
  public String visitExpr(Expr term)
  {
    throw new ZEvesIncompatibleASTException("Expression", term);
  }

  @Override
  public String visitPowerExpr(PowerExpr term)
  {
    return format(POWER_EXPR_PATTERN, getExpr(term.getExpr()));
  }

  @Override
  public String visitRefExpr(RefExpr term)
  {
    /* NOTE (from Z.xsd):
     *
     * A reference expression (C.6.21, C.6.28, C.6.29).
     *
     * C.6.21 (Generic Operator Application).  For example: S \rel T.
     *       In this case, mixfix is always true and the list of
     *       type expressions is non-empty (it contains [S,T]).
     *
     *  (IN THIS CASE, IT COMES FROM ExprPred!)
     *
     * C.6.28 (Reference).  For example: \emptyset.
     *       In this case, mixfix is always false and the list of
     *       type expressions is empty.</li>
     * C.6.29 (Generic Instantiation).  For example: \emptyset[T].
     *       In this case, mixfix is always false and the list of
     *       type expressions is non-empty (it contains [T]).
     */
    /* NOTE:
     *
     * This case is very, very tricky. Its precision will come with
     * time and testing. I am not sure about the way CZT and Z/Eves
     * generic actuals are allowed around.
     * Anyway, this seldom happens in most of Z/Eves proofs and
     * definitions one usually needs to deal with as proofs with
     * generic actuals around is bloody hard to do.
     * Another important point is about Generic (inferred) instantiations,
     * where the type [T] is inferred somewhere. I am assuming that,
     * if we omit then (because they were not present in the first place),
     * then Z/Eves will sort itself out, as in \\emptyset. Ok let's go!
     */
    String result;
    // case 6.21
    if (term.getMixfix())
    {

      // FIXME: (Leo): go through the RefExpr production properly here
      //			The solution below is best effort and incomplete
      ZExprList exprList = term.getZExprList();
      if (exprList.size() < 1 || exprList.size() > 2)
      {
        // AV: Can it be more/less than 2 here? Leo: No.
        throw new ZEvesIncompatibleASTException("CZT RefExpr generic operator application translation to Z/Eves is not yet implemented "
                                                + "(for \"" + term.getZName().toString() + "\").");
      }

      // pushes a RefExpr to the stack, yet with Mixfix True, then no need for ARG_TOK
      String opName = getRefName(term);
      if (opName == null || opName.equals(""))
      {
        throw new ZEvesIncompatibleASTException("Relational operator could not be translated. See throwable cause for details.",
                new IllegalArgumentException("It wasn't possible to properly translate relational operator "
                                             + term.getZName().toString() + " into Z/Eves format."));
      }

      // AV: Ignore generics here? Leo: yes, as you cannot give it explicitly in this case?

      Expr left = exprList.get(0);

      // Leo: This is not treating possibly tricky (e.g., \\listarg) \\relation or \\generic operator templates?
      //      I think Z/Eves doesn't have them anyway. Should be fine in general.
      if (exprList.size() > 1)
      {
        Expr right = exprList.get(1);
        result = format(MIXFIX_REF_EXPR_PATTERN, getExpr(left), opName, getExpr(right));
      }
      else
      {
        // only left available - prefix
        // TODO why is Prefix here for Mixfix (term.getMixfix() == true)?
        result = format(PREFIX_REF_EXPR_PATTERN, opName, getExpr(left));
      }

//            throw new ZEvesIncompatibleASTException("CZT RefExpr generic operator application translation to Z/Eves is not yet implemented " +
//                    "(for \"" + term.getZName().toString() + "\").");
      // others are more straightforward.
    }
    // case 6.28, 6.29
    else
    {
      String genActuals = "";
      result = "";
      if (!term.getZExprList().isEmpty() && term.getExplicit() != null && term.getExplicit())
      {
        genActuals = getGenActuals(term.getZExprList());
        result += "(";
      }
      // Don't call getRefName here, but name directly (e.g., name not to be treated as a possible operator).
      // e.g., for ApplExpr with mixfix true RefExpr has mixfix false, but shouldn't get operators              (x + y) or (\_R\_) \comp (\_ S\_)
      //       whereas for ApplExpr with mixfix false RefExpr also has mixfix false, but *must* get operators!  (_+_)(x,y) (\_\comp\_)((\_R\_), (\_S\_))
      result += getName(term.getName());
      if (!genActuals.isEmpty())
        // because of the postfix function case, say (f) (( _ &suptilde;)[X, Y]), we need to have (f) (&suptilde;[X, Y])
        // that is, ZEves is happy with operators close to their generics, so long as they don't have VARARGS?
      {
        // for _ &xxx; _  have it as: (_ &xxx; _)[X]
        if (result.split(ZString.ARG).length > 2)
          result += ")" + genActuals;
        // for &xxx; _  or _ &xxx; have it as: (&xxx;[X])
        else
          result += genActuals + ")";
      }
    }
    assert result != null && !result.equals("");
    return result;
  }

  @Override
  public String visitNegExpr(NegExpr term)
  {
    return format(NEG_EXPR_PATTERN, getExpr(term.getExpr()));
  }

  @Override
  public String visitMuExpr(MuExpr term)
  {
    String schText = term.getSchText().accept(this).toString();
    String expr = "";
    if (term.getExpr() != null)
    {
      expr = " &bullet; " + getExpr(term.getExpr());
    }
    return "&mu; " + schText + expr;
  }

  @Override
  public String visitSetCompExpr(SetCompExpr term)
  {
    // TODO review corner cases like \{ T \} and \{ T | true \} when T == [ ... | ... ] schema
    String schText = term.getSchText().accept(this).toString();
    String expr = "";
    if (term.getExpr() != null)
    {
      expr = " &bullet; " + getExpr(term.getExpr());
    }
    return "{ " + schText + expr + " }";
  }

  @Override
  public String visitLambdaExpr(LambdaExpr term)
  {
    return format(LAMBDA_EXPR_PATTERN, "&lambda;",
            term.getSchText().accept(this).toString(), getExpr(term.getExpr()));
  }

  @Override
  public String visitQntExpr(QntExpr term)
  {
    /* NOTE: This case covers quatifiers Exists, Exists1, and Forall.
     */

    // Differently from QntPred, we *cannot* have operator templates in qnt schema expressions! Schemas are not part of operators.
    return format(QNT_EXPR_PATTERN, getQntName(term), term.getSchText().accept(this), getExpr(term.getExpr()));
  }

  @Override
  public String visitLetExpr(LetExpr term)
  {
    throw new ZEvesIncompatibleASTException("CZT Let expression/predicate term "
                                            + "contains a SchText where Z/Eves expects a led-def production. "
                                            + "This translation is complex and requires effort not yet implemented "
                                            + "in this version, sorry.");
    //return format(LET_EXPR_PATTERN, getLetDef(term.getSchText()), getExpr(term.getExpr()));
  }

  @Override
  public String visitTupleSelExpr(TupleSelExpr term)
  {
    return format(TUPLESEL_EXPR_PATTERN, getExpr(term.getExpr()), term.getNumeral().toString());
  }

  @Override
  public String visitPreExpr(PreExpr term)
  {
    return format(PRE_EXPR_PATTERN, getExpr(term.getExpr()));
  }

  @Override
  public String visitSetExpr(SetExpr term)
  {
    StringBuilder sb = new StringBuilder("{ ");
    if (!term.getZExprList().isEmpty())
    {
      fZExprListSep = ", ";
      sb.append(term.getZExprList().accept(this));
    }
    sb.append(" }");
    return sb.toString();
  }

  @Override
  public String visitNumExpr(NumExpr term)
  {
    return term.getValue().toString();
  }

  @Override
  public String visitCondExpr(CondExpr term)
  {
    return format(COND_EXPR_PATTERN, getPred(term.getPred()),
            getExpr(term.getLeftExpr()), getExpr(term.getRightExpr()));
  }

  @Override
  public String visitProdExpr(ProdExpr term)
  {
    fZExprListSep = "&cross; ";
    return "(" + term.getZExprList().accept(this) + ")";
  }

  @Override
  public String visitTupleExpr(TupleExpr term)
  {
    fZExprListSep = ", ";
    return "(" + term.getZExprList().accept(this) + ")";
  }

  @Override
  public String visitBindExpr(BindExpr term)
  {
    if (term.getZDeclList().isEmpty())
    {
      emptyDeclPartException();
    }
    StringBuilder result = new StringBuilder();
    String delim = "";
    for (Decl d : term.getZDeclList())
    {
      assert d instanceof ConstDecl;
      ConstDecl cd = (ConstDecl)d;
      result.append(delim);
      result.append(getName(cd.getName()));
      result.append(": ");
      result.append(getExpr(cd.getExpr()));
      delim = "; ";
      result.append(delim);
    }
    return format(BIND_EXPR_PATTERN, result.toString());
  }

  @Override
  public String visitBindSelExpr(BindSelExpr term)
  {
    if (!(term.getExpr() instanceof RefExpr))
    {
      throw new ZEvesIncompatibleASTException("Z/Eves only allows bind selection for schema references, "
                                              + "rather than schema expressions. See throwable cause for details.",
              new IllegalArgumentException("Invalid schema expression binding selection for Z/Eves XML translation. CZT and"
                                           + "the Z Standard allow bind selection upon schema expressions, such as (S \\land T).x or (\\theta S).x."
                                           + "On the other hand, Z/Eves only accepts bind selection upon schema-ref, which must be a reference name to a "
                                           + "previously declared schema. The solution for this is simple: rewrite the specification so that these references "
                                           + "do not appear. TODO: In a later version, we plan to automatically include such declarations implicitly, while "
                                           + "translating the binding selection itself. Check whether a new version with such feature is available."));
    }
    return format(BINDSEL_EXPR_PATTERN, getExpr((RefExpr) term.getExpr()), getVarName(term.getZName()));
  }

  @Override
  public String visitThetaExpr(ThetaExpr term)
  {
    Expr e = term.getExpr();
    if (!(e instanceof RefExpr || e instanceof DecorExpr || e instanceof RenameExpr))
    {
      throw new ZEvesIncompatibleASTException("Z/Eves only allows theta expressions to schema references, "
                                              + "rather than schema expressions. See throwable cause for details.",
              new IllegalArgumentException("Invalid theta expression for Z/Eves XML translation. CZT and"
                                           + "the Z Standard allow theta expressions of schema expressions, such as \\theta(S \\land T)."
                                           + "On the other hand, Z/Eves only accepts theta expressions of schema-ref, which must be a reference name to a "
                                           + "previously declared schema. The solution for this is simple: rewrite the specification so that these references "
                                           + "do not appear. Some examples where there dependencies on the values (e.g. Circcus Operational Semantics) this is "
                                           + "not possible to naively translate and need to be rewritten, tough. TODO: In a later version, we plan to automatically "
                                           + "include such declarations implicitly whenever possible, while translating the binding selection itself. "
                                           + "Check whether a new version with such feature is available."));
    }
    return format(THETA_EXPR_PATTERN, getExpr(term.getExpr()), getStrokes(term.getZStrokeList()));
  }

  @Override
  public String visitSchExpr2(SchExpr2 term)
  {
    /* NOTE:
     * This production covers: CompExpr, PipeExpr, ProjExpr, AndExpr,
     * OrExpr, ImpliesExpr, and IffExpr.
     */
    return format(BIN_SCHEXPR_PATTERN, getExpr(term.getLeftExpr()), getSchExprOpName(term), getExpr(term.getRightExpr()));
  }

  @Override
  public String visitSchExpr(SchExpr term)
  {
    return "[" + term.getSchText().accept(this).toString() + "]";
  }

  @Override
  public String visitHideExpr(HideExpr term)
  {
    return format(HIDE_EXPR_PATTERN, getExpr(term.getExpr()), term.getZNameList().accept(this));
  }

  @Override
  public String visitApplExpr(ApplExpr term)
  {
    final String result;
    /**
     * A function application (C.6.21, C.6.22).
     *   <ul>
     *   <li>C.6.21 (Function Operator Application).  For example: S + T.
     *           In this case, Mixfix=true, the first (left) expression is the
     *           name, (" _ + _ "), (that is, a RefExpr with Mixfix=false!)
     *           and the second (right) expression is (S,T).</li>
     *   <li>C.6.22 (Application).  For example: (_ + _)(S, T).
     *           In this case, Mixfix=false, and the rest is the same as above
     *           (the first expression is the RefExpr with Mixfix=false and
     *           name (" _ + _ "), and the second expression is (S,T)).
     *           Another example: dom R.
     *           In this case, Mixfix=false, the first (left) expression is the
     *           function, dom, (again, a RefExpr with Mixfix=false)
     *           and the second (right) expression is the argument R.</li>
     */
    // case 6.21
    if (ZUtils.isFcnOpApplExpr(term))
    {
      assert term.getMixfix() != null && term.getMixfix();

      Expr opExpr = ZUtils.getApplExprRef(term);
      String op = getApplExprPart(term);

      int arity = ZUtils.applExprArity(term);
      ZExprList args = ZUtils.getApplExprArguments(term);
        
      // Handling special cases known to Z/Eves

      // LANGLE / RANGLE
      if (op.equals("&lang;&rang;"))
      {
        assert args.size() == 1 &&
               args.get(0) instanceof SetExpr; // SetExpr with all the elements enumerated... < a, b > =  (<,,>)({(1,a), (2,b)})
        SetExpr elems = (SetExpr)args.get(0);
        StringBuilder seqElems = new StringBuilder();
        String delim = "";
        for (Expr e : elems.getZExprList())
        {
          seqElems.append(delim).append(extractSeqElem(e));
          delim = ", ";
        }
        result = format(APPL_EXPR_SEQ_PATTERN, seqElems);
      }
      // LIMG / RIMG
      else if (op.equals("&lvparen;&rvparen;"))
      {
        assert args.size() == 2;
        result = format(MIXFIX_APPL_EXPR_RELIMAGE_PATTERN, getExpr(args.get(0)), getExpr(args.get(1)));
      }
      // all other cases
      else
      {
        // ex:  (\_ r \_) \comp (\_ s \_)  : ApplExpr(\comp, (r, s)) but as operators with \_!
        List<String> params = new ArrayList<String>(args.size());
        params.add(op);
        // tell potential RefExpr as operators (e.g., mixfix false) about a ApplExpr
        //fRelationalOpAppl.push(term);
        for (Expr e : args)
        {
          // push the expr. If it is a refExpr, check whether the mixfix is false, and if so, get ARG_TOK
          fRelationalOpAppl.push(e);
          params.add(getExpr(e));
          checkStack(e);
        }
        assert params.size() == args.size() + 1;
        //checkStack(term);
        switch (arity)
        {
          case 1:
            assert params.size() == 2; // op + arg (e.g., _\inv)
            if (getFixity(opExpr) == Fixity.POSTFIX)
            {
            	result = format(POSTFIX_APPL_EXPR_PATTERN, params.toArray());
            } 
            else
            {
            	// sometimes this happens (e.g. in #A), use the same as default ApplExpr
            	result = format(APPL_EXPR_PATTERN, params.toArray());
            }
            break;
          case 2:
            assert params.size() == 3; // arg + op + arg (e.g., _ + _)
            result = format(MIXFIX_APPL_EXPR_PATTERN, params.toArray());
            break;
          default:
            throw new ZEvesIncompatibleASTException("Unsupported operator template application expression " + arity + " params as " + params, term);
        }
      }
    }
    // case 6.22
    else
    {
      String op = getApplExprPart(term);
      String rhs = getExpr(term.getRightExpr());
      rhs = adjustIfOpWithinArgument(rhs);
      // TODO: find better way for this HACK!?
      // if this is a complex ApplExpr (e.g., has "_" or multiple appls, or hard spaces for other applexpr already)
      if (op.indexOf(ZString.ARG) != -1 || op.indexOf(ZString.LPAREN) != -1 || op.indexOf("~") != -1 || op.indexOf(ZString.SPACE) != -1)
        op = "(" + op + ")";
      // if the RHS is a tupleExpr, there will be more than one parameter, need parenthesis;
      if (term.getRightExpr() instanceof TupleExpr)// || rhs.indexOf(ZString.COMMA) != -1)
        rhs = "(" + rhs + ")";
      // if just a ZEves operator name (with or without generics) that is parenthesised, eg  (&xxxx;) or (&xxxx;[X,Y])
      else if (rhs.startsWith("(&") && (rhs.endsWith(";)") || (rhs.endsWith("])") && rhs.indexOf(";[") != -1)))
        rhs = rhs.substring(1, rhs.length()-1);
      result = format(APPL_EXPR_PATTERN_2, op, rhs);
    }
    return result;
  }
  
  private Fixity getFixity(Expr opTerm) {
	  if (opTerm instanceof RefExpr) {
		  RefExpr opRef = (RefExpr) opTerm;
		  OperatorName opName = opRef.getZName().getOperatorName();
		  if (opName != null) {
			  return opName.getFixity();
		  }
	  }
	  
	  return null;
  }

  @Override
  public String visitDecorExpr(DecorExpr term)
  {
    return getExpr(term.getExpr()) + term.getStroke().accept(this);
  }

  protected Type2 getType(String sectionName, ZName name)
  {
    if (sectionName == null) {
      throw new IllegalArgumentException("No section name indicated for type information");
    }
    
    try
    {
      SectTypeEnvAnn sectTypeEnv = getSectionInfo().get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));
      Type2 result = null;
      for(NameSectTypeTriple nst : sectTypeEnv.getNameSectTypeTriple())
      {
        if (ZUtils.namesEqual(name, nst.getZName()))
        {
          Type type = nst.getType();
          result = GlobalDefs.unwrapType(type);
          break;
        }
      }
      return result;
    }
    catch (CommandException e)
    {
      throw new ZEvesIncompatibleASTException("Could not retrieve type information of section " + sectionName + " for " + name, e);
    }
  }

  protected boolean isSchemaTyped(String sectionName, ZName name)
  {
    Type2 type = getType(sectionName, name);
    return (type instanceof PowerType && ((PowerType)type).getType() instanceof SchemaType);
  }

  @Override
  public String visitRenameExpr(RenameExpr term)
  {
    final String renamings;
    if (term.getRenameList() instanceof ZRenameList)
      renamings = term.getZRenameList().accept(this);
    else if (term.getRenameList() instanceof InstantiationList)
    {
      InstantiationList il = ZEvesUtils.getInstantiationListFromExpr(term);
      if (il != null)
      {
        fCurrInstKind.push(InstantiationKind.ThmReplacement);
        renamings = il.accept(this);

        assert !fCurrInstKind.isEmpty();
        InstantiationKind k = fCurrInstKind.pop();
        assert k.equals(InstantiationKind.ThmReplacement);
      }
      else
        throw new ZEvesIncompatibleASTException("Rename expression might contains mixed instantiations and renamings from Z/Eves. Not supported");
    }
    else
      throw new ZEvesIncompatibleASTException("Rename expression might contains mixed instantiations and renamings from Z/Eves. Not supported");
    return format(RENAME_EXPR_PATTERN, getExpr(term.getExpr()), renamings);
  }
  
  @Override
  public String visitZRenameList(ZRenameList term)
  {
		StringBuilder sb = new StringBuilder();

    String delim = "";
    for (NewOldPair pair : term) {
      sb.append(delim).append(pair.accept(this));
      delim = ",";
    }

    return sb.toString();
  }

  @Override
  public String visitNewOldPair(NewOldPair term) {
    return getName(term.getNewName()) + "/" + getName(term.getOldName());
  }

  @Override
  public String visitProofScript(ProofScript term)
  {
    final String thmName = getName(term.getName());

    // list of proof commands useful for interactive send/receive as <cmd="proof-command"> command </cmd>
    List<String> pScript = proofScripts_.get(thmName);
    if (pScript != null)
    {
      CztLogger.getLogger(getClass()).info("Updating proof script for " + thmName);
      pScript.clear();
    }
    else
    {
      pScript = new ArrayList<String>(term.getProofCommandList().size());
      proofScripts_.put(thmName, pScript);
    }

    // list of proof commands separated by semi-colon for "<proof-part/>" inlined proof commands
    StringBuilder proofCommands = new StringBuilder();
    String delim = "";
    for (ProofCommand pc : term.getProofCommandList())
    {
      final String pcStr = pc.accept(this);
      proofCommands.append(delim).append(pcStr);
      delim = "; \n";
      pScript.add(wrapProofCommand(pcStr));
    }

    // returns inlined-proofs as <proof-part/>
    return format(ZEVES_PROOF_PART_PATTERN, proofCommands.toString());
  }

  /**
   * For every zproof available, return corresponding proof scripts
   * @param thmName
   * @return
   */
  public List<String> getProofScripts(String thmName)
  {
    List<String> result = proofScripts_.get(thmName);
    if (result != null)
      result = Collections.unmodifiableList(result);
    return result;
  }

  public Set<String> getThmNamesWithProofScripts()
  {
    return Collections.unmodifiableSet(proofScripts_.keySet());
  }

  @Override
  public String visitProofCommand(ProofCommand term)
  {
    throw new ZEvesIncompatibleASTException("ProofCommand", term);
  }

  @Override
  public String visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    switch (term.getKind())
    {
      case Cases:
        return "cases";
      case Next:
        return "next";
      case Split:
        return "split " + getPred(term.getPred());
      default:
        throw new ZEvesIncompatibleASTException(
                "Unsupported case analysis kind: " + term.getKind());
    }
  }

  @Override
  public String visitNormalizationCommand(NormalizationCommand term)
  {
    switch (term.getKind())
    {
      case Conjunctive:
        return "conjunctive";
      case Disjunctive:
        return "disjunctive";
      case Rearrange:
        return "rearrange";
      case Command:
        return "with normalization " + term.getProofCommand().accept(this);
      default:
        throw new ZEvesIncompatibleASTException(
                "Unsupported normalization command kind: " + term.getKind());
    }
  }

  @Override
  public String visitQuantifiersCommand(QuantifiersCommand term)
  {
    StringBuilder result = new StringBuilder();
    if (term.getInstantiationList() == null || term.getInstantiationList().isEmpty())
    {
      result.append("prenex");
    }
    else
    {
      assert term.getInstantiationList() != null && !term.getInstantiationList().isEmpty() : "quantifiers instantiation list cannot be empty";
      result.append("instantiate ");
      fCurrInstKind.push(InstantiationKind.Quantifier);
      result.append(term.getInstantiationList().accept(this));
      assert !fCurrInstKind.isEmpty();
      InstantiationKind k = fCurrInstKind.pop();
      assert k.equals(InstantiationKind.Quantifier);
    }
    return result.toString();
  }

  @Override
  public String visitInstantiation(Instantiation term)
  {
    assert !fCurrInstKind.isEmpty();
    InstantiationKind k = fCurrInstKind.peek();
    assert k.equals(term.getKind()) : "inconsistent instantiation kind. found "
                                             + term.getKind() + "; expected " + k;
    StringBuilder result = new StringBuilder();
    result.append(getName(term.getZName()));
    result.append(k.equals(InstantiationKind.Quantifier) ? " == " : " := ");
    // instantiations *must* also allow for opArgs because of potential need of
    // explicit generics. Z/Eves accepts "\#[X]~A", whereas CZT insists on "(\#~\_)[X]~A"
    // so we almost always need to add the full (no-fix) version of op-temp names in inst.
    fRelationalOpAppl.push(Boolean.TRUE);
    result.append(getExpr(term.getExpr()));
    checkStack(Boolean.TRUE);
    return result.toString();
  }

  @Override
  public String visitInstantiationList(InstantiationList term)
  {
    StringBuilder result = new StringBuilder();
    Iterator<Instantiation> it = term.iterator();
    assert !fCurrInstKind.isEmpty() : "visiting instantiation list outside any instantiation context";
    assert it.hasNext() : "empty instantiations are not allowed for instantiation kind "
                          + fCurrInstKind.peek();
    while (it.hasNext())
    {
      result.append(it.next().accept(this));
      if (it.hasNext())
      {
        result.append(",");
      }
    }
    return result.toString();
  }

  @Override
  public String visitSimplificationCommand(SimplificationCommand term)
  {
    switch (term.getKind())
    {
      case Reduce:
        switch (term.getPower())
        {
          case None:
            return "reduce";
          case Prove:
            return "prove by reduce";
          case Trivial:
            throw new ZEvesIncompatibleASTException(
                    "Trivial reduce is not supported by Z/Eves");
          default:
            throw new ZEvesIncompatibleASTException(
                    "Unsupported simplification command power: " + term.getPower());
        }
      case Rewrite:
        switch (term.getPower())
        {
          case None:
            return "rewrite";
          case Prove:
            return "prove by rewrite";
          case Trivial:
            return "trivial rewrite";
          default:
            throw new ZEvesIncompatibleASTException(
                    "Unsupported simplification command power: " + term.getPower());
        }

      case Simplify:
        switch (term.getPower())
        {
          case None:
            return "simplify";
          case Prove:
            throw new ZEvesIncompatibleASTException(
                    "Prove by simplify is not supported by Z/Eves");
          case Trivial:
            return "trivial simplify";
          default:
            throw new ZEvesIncompatibleASTException(
                    "Unsupported simplification command power: " + term.getPower());
        }

      default:
        throw new ZEvesIncompatibleASTException(
                "Unsupported simplification command kind: " + term.getKind());
    }
  }

  @Override
  public String visitUseCommand(UseCommand term)
  {
    StringBuilder result = new StringBuilder("use ");
    
    // don't use visitRefExpr here to avoid confusion of the name as an operator
    // with explicit generics. Instead, visit each part of the name.
    RefExpr useName = term.getTheoremRef();
    result.append(getName(useName.getName()));
    if (useName.getExprList() != null && !useName.getZExprList().isEmpty())
      result.append(getGenActuals(useName.getZExprList()));
    if (term.getInstantiationList() != null)
    {
      fCurrInstKind.push(InstantiationKind.ThmReplacement);
      if (!term.getInstantiationList().isEmpty())
      {
        result.append("[");
        result.append(term.getInstantiationList().accept(this));
        result.append("]");
      }

      assert !fCurrInstKind.isEmpty();
      InstantiationKind k = fCurrInstKind.pop();
      assert k.equals(InstantiationKind.ThmReplacement);
    }
    return result.toString();
  }

  @Override
  public String visitWithCommand(WithCommand term)
  {
    assert term.getProofCommand() != null : "with command must have an inner command";
    StringBuilder result = new StringBuilder("with ");
    if (term.getExpr() != null)
    {
      assert term.getPred() == null : "with expression command cannot have pred"; // && term.getZNameList().isEmpty();
      result.append("expression (");
      result.append(getExpr(term.getExpr()));
      result.append(") ");
    }
    else if (term.getPred() != null)
    {
      assert term.getExpr() == null : "with predicate command cannot have expr";
      result.append("predicate (");
      result.append(getPred(term.getPred()));
      result.append(") ");
    }
    else if (term.getEnabled() != null)
    {
      assert term.getExpr() == null && term.getPred() == null
             && term.getNameList() instanceof ZNameList && !term.getZNameList().isEmpty() : "with enabled/disabled command cannot have expr or pred and name list must not be empty";
      result.append(term.getEnabled() ? "enabled " : "disabled ");
      result.append("(");
      result.append(getNameList(term.getZNameList().iterator(), true));
      result.append(") ");
    }
    else
    {
      throw new ZEvesIncompatibleASTException(
              "Unsupported with command: " + term);
    }
    result.append(term.getProofCommand().accept(this));
    return result.toString();
  }

  @Override
  public String visitSubstitutionCommand(SubstitutionCommand term)
  {
    assert term.getProofCommand() == null && term.getNameList() == null
           || term.getNameList() instanceof ZNameList : "subst command must have a subcmd and a Z namelist";
    switch (term.getKind())
    {
      case Invoke:
        assert term.getExpr() == null : "invoke command cannot have an expression";
        if (term.getPred() != null)
        {
          return "invoke predicate " + getPred(term.getPred());
        }
        else if (term.getNameList() == null || term.getZNameList().isEmpty())
        {
          return "invoke";
        }
        else
        {
          assert term.getNameList() != null && term.getZNameList().size() == 1 : "invoke cmd only on a single name";
          return "invoke " + getDefLHS(ZUtils.assertZName(term.getZNameList().get(0)));
        }
      case Equality:
        assert term.getPred() == null : "equality substitute command cannot have a predicate";
        if (term.getExpr() != null)
        {
          return "equality substitute " + getExpr(term.getExpr());
        }
        else
        {
          return "equality substitute";
        }
      default:
        throw new ZEvesIncompatibleASTException(
                "Unsupported substition command kind: " + term.getKind());
    }
  }

  @Override
  public String visitApplyCommand(ApplyCommand term)
  {
    assert term.getProofCommand() == null && term.getNameList() != null
           && term.getNameList() instanceof ZNameList && term.getZNameList().size() == 1 : "apply command cannot have subcommand and must have a singleton Z namelist";
    StringBuilder result = new StringBuilder("apply ");
    result.append(getName(term.getZNameList().get(0)));
    if (term.getPred() != null)
    {
      assert term.getExpr() == null : "apply to predicate cannot have an expression";
      result.append(" to predicate ");
      result.append(getPred(term.getPred()));
    }
    else if (term.getExpr() != null)
    {
      assert term.getPred() == null : "apply to expression cannot have an predicate";
      result.append(" to expression "); // )");
      result.append(getExpr(term.getExpr()));
      // result.append(")");
    }
    return result.toString();
  }

  /**
   * Returns a comma-separated list of toolkit names, where standard Z toolkit names are not
   * included as they are loaded in Z/Eves by default. Moreover, user sections must NOT be
   * named "toolkit" as this is a reserved name for Z/Eves.
   * <p>
   * We are not yet processing parents outside the standard toolkit, as surprisingly the Z/Eves
   * does not yet implement sectioning. That means the available Z/Eves GUI's include this
   * separately.
   * </p>
   * @param parents
   * @return
   */
  public static String getParents(List<Parent> parents)
  {
    StringBuilder sb = new StringBuilder(ZEVES_TOOLKIT_NAME);
    Iterator<Parent> it = parents.iterator();
    while (it.hasNext())
    {
      Parent p = it.next();
      String sect = p.getWord();
      if (sect.equals(ZEVES_TOOLKIT_NAME))
      {
        throw new ZEvesIncompatibleASTException("\"toolkit\" is a reserved section name for Z/Eves use only.");
      }
      // Include only user defined toolkits, rather than the standard ones.
      if (!Z_TOOLKIT_NAMES.contains(sect))
      {
        // AV: Z/Eves actually does not support commas here, and names should be space-separated
        sb.append(" ");
//                sb.append(", ");
        sb.append(p.getWord());
      }
    }
    return sb.toString();
  }

  /**
   * Special visitor class to translate top-level Z terms.
   * Each element in the returned list must be transmitted to the Z/Eves
   * server separately, in the given order.
   */
  private class SpecPrinter implements
          TermVisitor<List<String>>,
          SpecVisitor<List<String>>,
          ZSectVisitor<List<String>>,
          NarrSectVisitor<List<String>>
  {

    /**
     * Throws an exception for unexpected items.
     */
    @Override
    public List<String> visitTerm(Term term)
    {
      throw new ZEvesIncompatibleASTException("term", term);
    }

    @Override
    public List<String> visitNarrSect(NarrSect term)
    {
      List<String> result = new ArrayList<String>();
      result.add(comment("Narrative Section", ""));
      for (Object o : term.getContent())
      {
        if (o instanceof Term)
          result.add(((Term)o).accept(CZT2ZEvesPrinter.this));
        else
          result.add(o.toString());
      }
      return result;
    }

    /**
     * <p>
     * Returns a list of strings containing Z/Eves XML commands.
     * The first and last commands in the list are always those for
     * beginning and ending a Z section.
     * </p>
     * <p>
     * The paragraphs of the section are inserted between those two in
     * the order they have been declared. Each of these strings must be
     * sent to Z/Eves separately.
     * </p>
     * <p>
     * As we assume well-type Z sections, Z/Eves ought always to return
     * a "zoutput" tag indicating sucessful command execution.
     * In the case a "zerror" is returned, an exception should be thrown
     * and the translation algorithm revised for bugs.
     * </p>
     */
    @Override
    public List<String> visitZSect(ZSect term)
    {
      List<String> result = new ArrayList<String>();
      result.add(format(ZSECTION_BEGIN_PATTERN, term.getName(),
              getParents(term.getParent())));
      // mark section name
      setSectionName(term.getName());
      for (Para p : term.getZParaList())
      {
        result.add(p.accept(CZT2ZEvesPrinter.this));
      }
      result.add(ZSECTION_END_PATTERN);
      return result;
    }

    /**
     * Translates the all sections within this specification following
     * the protocol for ZSect terms.
     * At the head of the returned list we include a comment containing
     * the information for the specification header.
     */
    @Override
    public List<String> visitSpec(Spec term)
    {
      List<String> result = new ArrayList<String>();
      result.add(comment("Specification Information",
              String.valueOf(term.getVersion())));
      for (Sect sect : term.getSect())
      {
        result.addAll(sect.accept(this));
      }
      return result;
    }
  }
}
/*
<cmd name="add-paragraph"><zed-box>[Name, Event]</zed-box></cmd>
<zoutput></zoutput>

<cmd name="add-paragraph"><theorem-def>test <ax-part/>0 &isin; {0,1,2}</theorem-def></cmd>
<zoutput></zoutput>

<cmd name="set-current-goal-name">test</cmd>
<zoutput></zoutput>

<cmd name="get-goal-proved-state">test</cmd>
<zoutput><name ident="false"/>
</zoutput>

<cmd name="proof-command">rewrite</cmd>
<zoutput></zoutput>

<cmd name="get-goal-proved-state">test</cmd>
<zoutput><name ident="true"/>
</zoutput>
 */
