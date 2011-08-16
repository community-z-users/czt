/*
 * ZPrinter.java
 *
 * Created on 15 September 2005, 11:08
 */
package net.sourceforge.czt.zeves.z;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
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
import java.util.TreeMap;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.SectionInfo;
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
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
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
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.TupleSelExpr;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BindExprVisitor;
import net.sourceforge.czt.z.visitor.BindSelExprVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
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
        HideExprVisitor<String>, ApplExprVisitor<String>, DecorExprVisitor<String>, /*RenameExprVisitor<String>, */
        /* Proof command visitors */
        ProofCommandVisitor<String>, CaseAnalysisCommandVisitor<String>,
        NormalizationCommandVisitor<String>, QuantifiersCommandVisitor<String>,
        InstantiationVisitor<String>, InstantiationListVisitor<String>,
        SimplificationCommandVisitor<String>, UseCommandVisitor<String>,
        WithCommandVisitor<String>, SubstitutionCommandVisitor<String>,
        ApplyCommandVisitor<String>, ProofScriptVisitor<String>, OptempParaVisitor<String>
{

  /**
   * CZT Section manger object. TODO: Check necessity of this.
   */
  private SectionInfo fSectionInfo;
  /**
   * Label annotations matter only for axiomatic and generic boxes.
   * The flag switches its processing on and off.
   */
  private boolean fCheckForLabelAnnotations;
  /**
   * Flag set at getRel(term) method in order to instruct reference visiting
   * to consider operator names as relational applications.
   * That is, when the flag is true, the translation considers "x \\leq y"
   * as  "x &leq; y", whereas when the flag is false, the translatin considers
   * "(\\_ \\leq \\_)~(x, y)". In other words, the former just translates the
   * operator symbol, whereas the second translates both the operator symbol
   * as well as the underscor ARG_TOK.
   */
  private boolean fRelationalOpAppl;
  private final SpecPrinter fSpecPrinter;
  /**
   * Separation string for expressions in a ZExprList (used during visitZExprList)
   */
  private String fZExprListSep;
  /**
   * Current instantiation kind (used during visitQuantifiersCommand and visitUseCommand)
   */
  private InstantiationKind fCurrInstKind = null;

  /**
   * Map containing proof command lists for corresponding theorem names.
   * They can be used for both batch mode proof as well as interactive
   */
  private final Map<String, List<String>> proofScripts_;


  /* Constructors */
  /** Creates a new instance of ZPrinter
   * @param si
   */
  public CZT2ZEvesPrinter(SectionInfo si)
  {
    super();
    fZExprListSep = null;
    fRelationalOpAppl = false;
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
    return format(ZEVES_COMMAND, "add-paragraph", zevesPara);
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
    else if (word.equals(ZString.BIGCUP))
    {
      result = "&bigcup;";
    }
    else if (word.equals(ZString.BIGCAP))
    {
      result = "&bigcap;";
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
    else
    {
      result = word;
    }
    return result;
  }

  private String getOperator(OperatorName opname)
  {
    // See revision 3986 in the repository if this fails.
    // I used to use opname.iterator, for what now is getWords().
    Iterator<String> parts = Arrays.asList(opname.getWords()).iterator();//opname.iterator();


    // We are concatenating the result. In almost all cases, one gets "THE" operator involved
    // since we are ignoring ARGs. On ocassional special cases (e.g., LANGLE, LIMG, LBLOT, user defined
    // \\listarg op temp), we need to treat it specially, hence we send the whole load of symbols involved.
    //
    // PS: Z/Eves does not accept \\listarg definition by the user.
    String result = "";
    if (fRelationalOpAppl)
    {
      int found = 0;
      while (parts.hasNext())
      {
        String part = parts.next().toString();
        // ignore the arguments: we will know if it's a list arg from ApplExpr arity.
        if (!part.equals(ZString.ARG) && !part.equals(ZString.LISTARG))
        {
          found++;
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
    else
    {
      throw new ZEvesIncompatibleASTException("Case yet to be handled: getOperator with " + opname + " that is not a relational op appl");
      //getFixity(opname.getFixity());
    }
    assert !result.isEmpty();
    return result;
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
  private String getStrokes(ZStrokeList strokes)
  {
    StringBuilder result = new StringBuilder("");
    for (Stroke stk : strokes)
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

  /**
   * Returns a comma-separated list of decl-name or ref-name (but not mixed).
   * It assumes the list is neither null nor empty. It is used to represent
   * various productions related to names with operators.
   */
  private String getNameList(Iterator<Name> it)
  {
    StringBuilder result = new StringBuilder("");
    ZName name = ZUtils.assertZName(it.next());
    result.append(getName(name));
    while (it.hasNext())
    {
      result.append(", ");
      name = ZUtils.assertZName(it.next());
      result.append(getName(name));
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
    return getVarName(dname);
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
  private String getGenFormals(ZNameList term)
  {
    assert term != null;
    StringBuilder result = new StringBuilder("");
    if (!term.isEmpty())
    {
      result.append("[");
      result.append(getIdentList(term));
      result.append("]");
      result.append(NL_SEP);
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

  /**
   * Retrieve the Z/Eves XML for the given non-null expression, something
   * the calling method must ensure, otherwise a NullPointerException (or
   * indeed an AssertionError) is thrown . Therefore, it always return some non-empty string.
   */
  private String getExpr(Expr expr)
  {
    assert expr != null;
    return expr.accept(this).toString();
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
      if (op.equals(And.Wedge))
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
  private String getMemPredRelOpName(RefExpr refexpr)
  {
    fRelationalOpAppl = true;
    String result = getExpr(refexpr);
    fRelationalOpAppl = false;
    if (result == null || result.equals(""))
    {
      throw new ZEvesIncompatibleASTException("Relational operator could not be translated. See throwable cause for details.",
              new IllegalArgumentException("It wasn't possible to properly translate relational operator "
                                           + refexpr.getZName().toString() + " into Z/Eves format."));
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
      // FIXME does not work for theorems - need semicolon instead of NL
      // trouble is CZT is more lenient/Iso-ZStd regarding spaces/NL here.
      // Z/Eves has a stricter encoding, yet it's allowed in certain places
      // (e.g., ConjPara or within Proof Commands
      result.append(NL_SEP); // sep chosen to be NL
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
    result.append(getExpr(e));
    while (it.hasNext())
    {
      result.append(fZExprListSep);
      e = it.next();
      result.append(getExpr(e));
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
    int prec = term.getPrec().intValue();
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
    final String result = format(OEPRATOR_TEMPLATE_PATTERN, operator, opClass);
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

    // AV: quite a hack, but we cannot have NL in axiom part here, however they get generated in #visitZDeclList()
    // TODO implement propertly - use semicolons in the generation
    // Currently replacing NLs with semicolons
    axiomPart = axiomPart.replace(NL_SEP, SC_SEP);

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
            lName, NL_SEP + getGenFormals(term.getZNameList()),
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
    String genFormals = getGenFormals(term.getZNameList());
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
       * part is empty.
       */
      String decls = "";
      String preds = getAxiomPart(schText.getPred());
      if (!isPredicatePara(schText))
      {
        fRelationalOpAppl = true;
        decls = getDeclPart(schText.getZDeclList());
        fRelationalOpAppl = false;
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
      fCheckForLabelAnnotations = true;
      String preds = getAxiomPart(term.getZSchText().getPred());
      fCheckForLabelAnnotations = false;
      if (!isPredicatePara(term.getSchText()))
      {
        fRelationalOpAppl = true;
        decls = getDeclPart(term.getZSchText().getZDeclList());
        fRelationalOpAppl = false;
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
      boolean isSchExpr = expr instanceof SchExpr || expr instanceof SchExpr2;
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
    return format(QNT_PRED_PATTERN, getQntName(term), term.getSchText().accept(this).toString(), getPred(term.getPred()));
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
    MemPredKind kind = getMemPredKind(term);
    String rel, left, right;
    switch (kind)
    {
      case SET_MEMBERSHIP:
        left = getExpr(term.getLeftExpr());
        rel = "&isin;";
        right = getExpr(term.getRightExpr());
        break;
      case NARY_RELOP_APPLICATION:
        ZExprList params = ((TupleExpr) term.getLeftExpr()).getZExprList();
        assert !params.isEmpty();
        if (params.size() != 2)
        {
          throw new ZEvesIncompatibleASTException("Current version only supports translation of binary relational operators.");
        }
        left = getExpr(params.get(0));
        rel = getMemPredRelOpName((RefExpr) term.getRightExpr());
        right = getExpr(params.get(1));
        break;
      case UNARY_RELOP_APPLICATION:
        RefExpr refexpr = (RefExpr) term.getRightExpr();
        OperatorName.Fixity fixity = refexpr.getZName().getOperatorName().getFixity();
        rel = getMemPredRelOpName(refexpr);
        /* NOTE:
         * The actual unary parameter comes from the left expression and is placed according to the fixture.
         */
        if (fixity == OperatorName.Fixity.PREFIX)
        {
          // Prefix: left+rel+right = ""+rel+right
          left = "";
          right = getExpr(term.getLeftExpr());
        }
        else if (fixity == OperatorName.Fixity.POSTFIX)
        {
          // Postfix: left+rel+right = left+rel+""
          left = getExpr(term.getLeftExpr());
          right = "";
        }
        else
        {
          throw new ZEvesIncompatibleASTException("Unsupported fixture for relational operator (" + fixity.toString() + ").");
        }
        break;
      case EQUALITY:
        /* NOTE:
         *
         * For equality, the left expression is a Expr, whereas the
         * right expression must be a SetExpr containing only one element
         */
        left = getExpr(term.getLeftExpr());
        rel = " = ";
        right = getExpr(((SetExpr) term.getRightExpr()).getZExprList().get(0));
        break;
      default:
        throw new AssertionError("Invalid MemPredKind " + kind);
    }
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
    // case C.6.21 is tricky. leave it out for now.
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

      fRelationalOpAppl = true;
      String opName = getName(term.getZName());
      fRelationalOpAppl = false;
      if (opName == null || opName.equals(""))
      {
        throw new ZEvesIncompatibleASTException("Relational operator could not be translated. See throwable cause for details.",
                new IllegalArgumentException("It wasn't possible to properly translate relational operator "
                                             + term.getZName().toString() + " into Z/Eves format."));
      }

      // AV: Ignore generics here?

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
    else
    {
      String genActuals = "";
      if (!term.getZExprList().isEmpty() && term.getExplicit() != null && term.getExplicit())
      {
        genActuals = getGenActuals(term.getZExprList());
      }
      // TODO: Check names for appropriate translation.
      result = getName(term.getZName()) + genActuals;
      // TODO: Detal with replacements! Not yet implemented?
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
    return format(QNT_EXPR_PATTERN, getQntName(term), term.getSchText().accept(this).toString(), getExpr(term.getExpr()));
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
    return format(THETA_EXPR_PATTERN, getExpr(term.getExpr()));
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
    // TODO: Check whether this is ok or not.
    return term.getSchText().accept(this).toString();
  }

  @Override
  public String visitHideExpr(HideExpr term)
  {
    return format(HIDE_EXPR_PATTERN, getExpr(term.getExpr()), term.getZNameList().accept(this));
  }

  private String extractSeqElem(Expr e)
  {
    assert e instanceof TupleExpr;
    TupleExpr te = (TupleExpr)e;
    assert te.getZExprList().size() == 2;
    Expr seqElem = te.getZExprList().get(1);
    return getExpr(seqElem);
  }

  @Override
  public String visitApplExpr(ApplExpr term)
  {

//    	if (term.getMixfix()) {
    if (ZUtils.isFcnOpApplExpr(term))
    {
      assert term.getMixfix() != null && term.getMixfix();
      // mixfix: left expr is the operator, right expr is a tuple with args
      fRelationalOpAppl = true;
      //String op = getExpr(term.getLeftExpr());
      String op = getExpr(ZUtils.getApplExprRef(term));
      fRelationalOpAppl = false;

      int arity = ZUtils.applExprArity(term);
      ZExprList args = ZUtils.getApplExprArguments(term);
      List<String> params = new ArrayList<String>(args.size());
        
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
        return format(APPL_EXPR_SEQ_PATTERN, seqElems);
      }
      // LIMG / RIMG
      else if (op.equals("&lvparen;&rvparen;"))
      {
        assert args.size() == 2;
        return format(MIXFIX_APPL_EXPR_RELIMAGE_PATTERN, getExpr(args.get(0)), getExpr(args.get(1)));
      }
      else
      {
        params.add(op);
        for (Expr e : args)
        {
          params.add(getExpr(e));
        }
        assert params.size() == args.size() + 1;
        switch (arity)
        {
          case 1:
            assert params.size() == 2; // op + arg
            // sometimes this happens (e.g. in #A), use the same as default ApplExpr
            return format(APPL_EXPR_PATTERN, params.toArray());
          case 2:
            assert params.size() == 3; // arg + op + arg
            return format(MIXFIX_APPL_EXPR_PATTERN, params.toArray());
          default:
            throw new ZEvesIncompatibleASTException("Unsupported operator template application expression " + arity + " params as " + params, term);
        }
      }
    }

    fRelationalOpAppl = true;
    String op = getExpr(term.getLeftExpr());
    fRelationalOpAppl = false;

    return format(APPL_EXPR_PATTERN, op, getExpr(term.getRightExpr()));
  }

  @Override
  public String visitDecorExpr(DecorExpr term)
  {
    return getExpr(term.getExpr()) + term.getStroke().accept(this);
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
      fCurrInstKind = InstantiationKind.Quantifier;
      result.append(term.getInstantiationList().accept(this));
    }
    return result.toString();
  }

  @Override
  public String visitInstantiation(Instantiation term)
  {
    assert fCurrInstKind == term.getKind() : "inconsistent instantiation kind. found "
                                             + term.getKind() + "; expected " + fCurrInstKind;
    StringBuilder result = new StringBuilder();
    result.append(getName(term.getZName()));
    result.append(fCurrInstKind == InstantiationKind.Quantifier ? " == " : " := ");
    result.append(getExpr(term.getExpr()));
    return result.toString();
  }

  @Override
  public String visitInstantiationList(InstantiationList term)
  {
    StringBuilder result = new StringBuilder();
    Iterator<Instantiation> it = term.iterator();
    assert it.hasNext() : "empty instantiations are not allowed for instantiation kind "
                          + fCurrInstKind;

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
    result.append(getExpr(term.getTheoremRef()));
    if (term.getInstantiationList() != null)
    {
      fCurrInstKind = InstantiationKind.ThmReplacement;
      if (!term.getInstantiationList().isEmpty())
      {
        result.append("[");
        result.append(term.getInstantiationList().accept(this));
        result.append("]");
      }
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
      result.append(getNameList(term.getZNameList().iterator()));
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
          return "invoke " + getName(term.getZNameList().get(0));
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
