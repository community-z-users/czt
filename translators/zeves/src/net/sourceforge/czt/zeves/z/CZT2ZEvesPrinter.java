/*
 * ZPrinter.java
 *
 * Created on 15 September 2005, 11:08
 */

package net.sourceforge.czt.zeves.z;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.ast.ZRefNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZExprListVisitor;
import net.sourceforge.czt.z.visitor.ZRefNameListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ZEvesIncompatibleException;
import java.text.MessageFormat;
import java.util.Iterator;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.BindSelExpr;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.CompExpr;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.FalsePred;
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
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.MuExpr;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.NumStroke;
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
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RefName;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SchText;
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
import net.sourceforge.czt.z.visitor.ZDeclNameVisitor;
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
import net.sourceforge.czt.z.visitor.ZRefNameVisitor;
import net.sourceforge.czt.z.visitor.SchExpr2Visitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SchTextVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.zeves.proof.ProofScript;
import net.sourceforge.czt.z.visitor.CondExprVisitor;
import net.sourceforge.czt.z.visitor.LambdaExprVisitor;
import net.sourceforge.czt.z.visitor.LetExprVisitor;
import net.sourceforge.czt.z.visitor.MuExprVisitor;
import net.sourceforge.czt.z.visitor.NegExprVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.PreExprVisitor;
import net.sourceforge.czt.z.visitor.ProdExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.TupleSelExprVisitor;

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
 * Whenever such incompatibility occurs, a ZEvesIncompatibleException is thrown
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
 * @author leo, 20/09/2005
 * @since 1.5
 */
public class CZT2ZEvesPrinter implements
        /* Special visitors */        
        TermVisitor<String>,  FreetypeVisitor<String>, SchTextVisitor<String>,
        ZDeclNameVisitor<String>, ZRefNameVisitor<String>,
        /* Z List visitors */
        ZDeclListVisitor<String>,  ZExprListVisitor<String>, ZRefNameListVisitor<String>, 
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
        ProdExprVisitor<String>, SetExprVisitor<String>, /*SetCompExprVisitor<String>,*/
        NumExprVisitor<String>, TupleExprVisitor<String>,
        TupleSelExprVisitor<String>, /*Qnt1ExprVisitor<String>, */ LambdaExprVisitor<String>,
        MuExprVisitor<String>, LetExprVisitor<String>, NegExprVisitor<String>, CondExprVisitor<String>, 
        PreExprVisitor<String>, ThetaExprVisitor<String>, BindSelExprVisitor<String>,
        BindExprVisitor<String>, SchExprVisitor<String>, SchExpr2Visitor<String>, 
        HideExprVisitor<String> /*, ApplExprVisitor<String>, DecorExprVisitor<String>, RenameExprVisitor<String>, */         
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
     * General message format used for various Z/Eves "XML" formatting.
     */
    private final MessageFormat fZEvesXMLFmt;
    
    /**
     * Separation string for expressions in a ZExprList (used during visitZExprList)
     */
    private String fZExprListSep;
    
    /**
     * VARIOUS STRINGS USED AS Z/EVES XML PATTERNS FOR FORMATTING OPERATIONS
     */
    
    private static final String SC_SEP = ";";
    public static final String EQ_SIGN = " = ";
    private static final String NL_SEP = System.getProperty("line.separator");
    
    
    public static final String ZEVES_COMMAND = "<cmd name=\"{0}\">\n{1}\n</cmd>";
    
    public static final String COMMENT_PATTERN = "<!-- \n *** {0} *** \n\n {1} \n-->";
    
    /* Special XML pattern strings */
    
    /**
     * {0} = number     => term.getNumber().toString()
     */
    public static final String NUM_STROKE_PATTERN = "&sub{0};";
    
    /**
     * {0} = var-name   => getVarName(term.getDeclName());
     * {1} = expr       => getExpr(term.getExpr());
     */
    public static final String BRANCH_PATTERN = "{0} &lchev {1} &rchev";
    
    /* z-paragraph XML pattern strings */
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = zboxItemName    => getSchName(((ConstDecl)term.getZSchText().getZDeclList()).getDeclName()); |
     *                          getDefLHS(((ConstDecl)term.getZSchText().getZDeclList()).getDeclName());
     * {3} = gen-formals     => getGenFormals(term.getDeclName());
     * {4} = zboxItemSymbol  => "&eqhat;" | "=="
     * {5} = zboxItemExpr    => getExpr(((ConstDecl)term.getZSchText().getZDeclList()).getExpr());
     */
    public static final String ZED_BOX_HORIZONTAL_PATTERN = "<zed-box {0} {1}>{2}\n{3}\n{4}\n{5}\n</zed-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = zboxItemNameList=> getIdentList(term.getDeclNames());
     */
    public static final String ZED_BOX_GIVENSET_PATTERN = "<zed-box {0} {1}>[{2}]</zed-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = zboxItemFreeType=> Build from getBranch for each branch.
     */
    public static final String ZED_BOX_FREETYPE_PATTERN = "<zed-box {0} {1}>{2}</zed-box>";
    
    /**
     * {0} = location           => getLocation(term);
     * {1} = ability            => getAbility(term);
     * {2} = labelled-predicate => getAxiomPart(term.getPred); with label option enabled.
     */
    public static final String PREDICATE_PARA_PATTERN = ZED_BOX_FREETYPE_PATTERN;
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = decl-part       => getDeclPart(term.getZSchText().getZDeclList());
     * {3} = axiom-part      => getAxiomPart(term.getSchText().getPred());
     */
    public static final String AXIOMATIC_BOX_PATTERN = "<axiomatic-box {0} {1}>\n{2}\n{3}\n</axiomatic-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = generic formals => getGenFormals(term.getDeclName());
     * {3} = decl-part       => getDeclPart(term.getZSchText().getZDeclList());
     * {4} = axiom-part      => getAxiomPart(term.getSchText().getPred());
     */
    public static final String GENERIC_BOX_PATTERN = "<generic-box {0} {1}>{2}\n{3}\n{4}\n</generic-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = schema-name     => getSchName(((ConstDecl)term.getZSchText().getZDeclList()).getDeclName());
     * {3} = generic formals => NL_SEP + getGenFormals(term.getDeclName());
     * {4} = decl-part       => getDeclPart(((SchExpr)((ConstDecl)term.getZSchText().getZDeclList()).getExpr()).getZSchText().getZDeclList());
     * {5} = axiom-part      => getAxiomPart(((SchExpr)((ConstDecl)term.getZSchText().getZDeclList()).getExpr()).getSchText().getPred());
     */
    private static final String SCHEMA_BOX_PATTERN = "<schema-box {0} {1}>{2}{3}\n{4}\n{5}\n</schema-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = usage           => getUsage(term);
     * {3} = theorem-name    => getTheoremName(term);
     * {4} = generic formals => NL_SEP + getGenFormals(term.getDeclName());
     * {5} = axiom-part      => getAxiomPart(term.getPred());
     * {6} = proof-part      => getProofPart(term);
     *
     * Note: Provided axiom-part is not empty.
     */
    public static final String THEOREM_DEF_PATTERN = "<theorem-def {0} {1} {2}>{3} {4}\n{5}\n{6}\n</theorem-def>";
    
    /**
     * {0} = ability      => label.getAbility();
     * {1} = usage        => label.getUsage();
     * {2} = theorem-name => label.getTheoremName();
     */
    public static final String LABEL_PATTERN = "&lchev; {0} {1} {2} &rchev;";
    
    /* predicate, predicate-1 XML pattern strings */
    
    /**
     * {0} = predicate      => getPred(term.getPred());
     */
    public static final String NEG_PRED_PATTERN = "&not; {0}";
    
    /**
     * {0} = quantifier     => getQntName(term); = "&exists;" | "&exists1;" | "&forall;"
     * {1} = schema-text    => term.getSchText.accept(this);
     * {2} = predicate      => getPred(term.getPred());
     */
    public static final String QNT_PRED_PATTERN = "{0} {1} &bullet; {2}";
    
    /**
     * {0} = predicate      => getPred(term.getLeftPred());
     * {1} = operator       => getBinPredName(term);  = "&wedge;" | &vee;" | "&rArr;" | "&hArr;"
     * {2} = predicate      => getPred(term.getRightPred());
     *
     * Note: "&wedge;" needs to be treated specially, as we want to consider
     *       labelled-predicates (i.e. each element on an AndPred having a Z/Eves label).
     *       For this case, we can only accept term.getOp() as And, Chain, or Semi,
     *       but not NL.
     */
    public static final String BIN_PRED_PATTERN = "{0} {1} {2}";
    
    /**
     * {0} expression   => getExpr(term.getLeftExpr());
     * {1} rel          => getRel(term); = "&isin;" | getRelOp(term) | "="
     * {2} expression   => getExpr(term.getRightExpr());
     *
     * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
     */
    public static final String MEMPRED_PATTERN = BIN_PRED_PATTERN;
    
    /* expression[-n] XML productions */
    
    /**
     * {0} expression       => getExpr(term.getExpr());
     */
    public static final String NEG_EXPR_PATTERN = "&neg; {0}";
    public static final String LAMBDA_EXPR_PATTERN = QNT_PRED_PATTERN;
    
    /**
     * {0} let-def          => getLetDef(term.getSchText());
     * {1} expression       => getExpr(term.getExpr());
     */
    public static final String LET_EXPR_PATTERN = "<word style=\"bold\"/>let<word/>{0} &bullet; {1}";
    
    /**
     * {0} expression       => getExpr(term.getExpr());
     *
     * NOTE: For Z/Eves this is a schema-ref, which here is simply a RefExpr.
     *       Nevertheless, care needs to be taken because in the translation of
     *       RefExpr as Z/Eves does not allow all forms of schema-expression that CZT allows.
     */
    public static final String PRE_EXPR_PATTERN = "<word style=\"roman\"/>pre<word/>{0}";
    
    /**
     * {0} expression       => getExpr(term.getExpr());
     * {1} number           => term.getSelect().toString();
     *
     * NOTE: To avoid problems, we always enclosed the expression within parenthesis.
     *       If those are redundant, the prover will remove then appropriately.
     *       TODO: Check this or ask Mark Saaltink directly.
     */
    public static final String TUPLESEL_EXPR_PATTERN = "({0}).{1}";
    public static final String BINDSEL_EXPR_PATTERN = TUPLESEL_EXPR_PATTERN;
    
    /**
     * {0} predicate        => getPred(term.getPred());
     * {1} expression       => getExpr(term.getLeftExpr());
     * {2} expression       => getExpr(term.getRightExpr());
     */
    public static final String COND_EXPR_PATTERN = "<word style=\"bold\"/>if<word/>{0}\n" +
            "<word style=\"bold\"/>then<word/>{1}\n" +
            "<word style=\"bold\"/>else<word/>{2}";
    
    /**
     * {0} expression       => getExpr(term.getExpr());
     *
     * NOTE: The expression can represent either a schema-ref dealt with through
     *       RefExpr or DecorExpr, or schema-ref replacements dealt with through
     *       a RenameExpr.
     */
    public static final String THETA_EXPR_PATTERN = "&theta; {0}";
    
    /**
     * {0} expression   => getExpr(term.getExpr());
     *
     * NOTE: For Z/Eves XML, CZT PowerExpr is just a special kind of var-name
     *       within expression-3, as there is no specific production for it.
     */
    public static final String POWER_EXPR_PATTERN = "&Popf; {0}";
    
    /**
     * {0} expression   => getExpr(term.getLeftExpr());
     * {1} sch-op-name  => getSchExprOpName(term); 
     * {2} expression   => getExpr(term.getRightExpr());
     *
     * NOTE: All SchExpr2 patterns: CompExpr, PipeExpr, ProjExpr, AndExpr, 
     *       OrExpr, ImpliesExpr, and IffExpr.     
     */
    public static final String BIN_SCHEXPR_PATTERN = MEMPRED_PATTERN;
    
    /**
     * {0} expression   => getExpr(term.getExpr());
     * {1} name list    => getZRefNameList.accept(this);
     */
    public static final String HIDE_EXPR_PATTERN = "{0} \\ ({1})";
    
    /* Constructors */
    
    /** Creates a new instance of ZPrinter */
    public CZT2ZEvesPrinter(SectionInfo si) {
        fZExprListSep = null;
        fRelationalOpAppl = false;
        fCheckForLabelAnnotations = false;
        fZEvesXMLFmt = new MessageFormat("");        
        fSpecPrinter = new SpecPrinter();
        setSectionInfo(si);
    }
    
    /* Auxiliary Methods */
    
    /**
     * Throws a ZEvesIncompatibleException due to empty declaration on paragraph boxes.
     */
    private void emptyDeclPartException() {
        throw new ZEvesIncompatibleException("Z/Eves does not accept empty declarations on paragraph boxes");
    }
    
    /**
     * Checks whether the inclusion expression is valid or not, providing
     * detailed information in the case it is. If it is valid, this method
     * returns null meaning there is no throwable "cause" to be concerned about.
     */
    private Throwable isValidZEvesInclDecl(Expr expr) {
        Throwable cause = null;
        if (!(expr instanceof DecorExpr || expr instanceof RenameExpr || expr instanceof RefExpr)) {
            cause = new IllegalArgumentException();
        }
        return cause;
    }
    
    /**
     * Check whether the given predicate is an AndPred split across multiple lines (i.e. has Op.NL).
     */
    private boolean isNLAndPred(Pred pred) {        
        return (pred instanceof AndPred && ((AndPred)pred).getAnd().equals(And.NL));
    }
    
    /**
     * Checks whether the given schema text has empty declarations or not. If it has, then
     * this should be a labelled-predicate or a predicate paragraph rather than an axiomatic/generic box.
     */
    private boolean isPredicatePara(SchText schText) {                        
        return ZUtils.assertZSchText(schText).getZDeclList().isEmpty();
    }
    
    /**
     * Returns wether the given term is a conjecture or not. Conjectures can contain ProofScript
     * annotations. The terms which allow proof script annotations are ConjPara or Pred.
     */
    private boolean isConjecture(TermA term) {
        return (term instanceof ConjPara || term instanceof Pred);
    }
    
    private boolean isPara(Term term) {
        return (term instanceof Para);
    }
    
    /**
     * Sets the formatting pattern for the underlying MessageFormat object.
     * This method is usually called right before method format.
     * To avoid interference by nested calls, this method should be called
     * right before the format argument.
     *
    private void setZEvesXMLPattern(String pattern) {
        fZEvesXMLFmt.applyPattern(pattern);
    }
    */
    
    /**
     * Applies the format operation from the underlying MessageFormat object
     * set to the last pattern. See constructor for the first pattern.
     * This method is usually called straight after method setZEvesXMLPattern.
     */
    private String format(String pattern, Object... arguments) {
        fZEvesXMLFmt.applyPattern(pattern);
        return fZEvesXMLFmt.format(arguments, new StringBuffer(), null).toString();
    }
    
    /**
     * Wraps-up a translated zevesPara within a Z/Eves XML command name "add-paragraph".
     */
    private String wrapPara(String zevesPara) {        
        return format(ZEVES_COMMAND, "add-paragraph", zevesPara);
    }
    
    private String comment(String headline, String text) {
        return format(COMMENT_PATTERN, headline, text);
    }
    
    /* Annotation related methods for Z/Eves productions not present in CZT */
    
    private Ability getAbilityAnn(TermA term) {
        if (!isPara(term))
            throw new IllegalArgumentException("Z/Eves location is allowed only for Para terms");
        return (Ability)term.getAnn(Ability.class);
    }
    
    private Location getLocationAnn(TermA term) {
        if (!isPara(term))
            throw new IllegalArgumentException("Z/Eves location is allowed only for Para terms");
        return (Location)term.getAnn(Location.class);
    }
    
    private Usage getUsageAnn(TermA term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves usage is allowed only for ConjPara and Pred terms");
        return (Usage)term.getAnn(Usage.class);
    }
    
    private Label getLabelAnn(TermA term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves label is allowed only for ConjPara and Pred terms");
        Label l = (Label)term.getAnn(Label.class);
        return l;
    }
    
    private ProofScript getProofScriptAnn(TermA term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves proof script is allowed only for ConjPara and Pred terms");
        ProofScript ps = (ProofScript)term.getAnn(ProofScript.class);
        return ps;
    }
    
    /**
     * Returns the string valued result for the current status of the ability flag
     * present as a term annotation.
     */
    private String getAbility(TermA term) {
        Ability a = getAbilityAnn(term);
        return a == null ? "" : a.toString().toLowerCase();
    }
    
    /**
     * Retrieves the location string attribute present as a term annotation.
     */
    private String getLocation(TermA term) {
        /* NOTE:
         *
         * Mark Saaltink said: "Locations are used in the GUI to record the origin of a paragraph (either from a file or from the GUI itself).
         * This is used so that if you re-import a LaTeX file after revising it, the appropriate paragraphs are updated. Just ignore it."
         */
        Location l = getLocationAnn(term);
        return l == null ? "" : "location="+l.getLocation();
    }
    
    /**
     * Retrieves the usage string attribute present as a term annotation.
     * Usage is only allowed for ConjPara and Pred, where IllegalArgumentException is
     * thrown for other terms.
     */
    private String getUsage(TermA term) {
        Usage u = getUsageAnn(term);
        return u == null ? "" : u.toString().toLowerCase();
    }
    
    private String getLabel(TermA term) {
        Label l = getLabelAnn(term);
        String result = "";
        if (l != null) {            
            result = format(LABEL_PATTERN, l.getAbility(), l.getUsage(), l.getTheoremName());
        } 
        return result;
    }
    
    /* Special Z/Eves API Productions */
    
    /**
     * Methods which implements Section 7 Entities, of the Z/Eves Core API
     */
    private String translateWord(String word) {
        if (word.startsWith(ZString.DELTA))
            word = "&Delta;" + word.substring(ZString.DELTA.length());
        else if (word.startsWith(ZString.XI))
            word = "&Xi;" + word.substring(ZString.XI.length());
        else if (word.startsWith(ZString.THETA))
            word = "&theta;" + word.substring(ZString.THETA.length());
        else if (word.equals(ZString.NAT))
            word = "&Nopf;";
        else if (word.equals(ZString.NUM))
            word = "&Zopf;";
        else if (word.equals(ZString.ARITHMOS))
            word = "&Aopf;";
        else if (word.equals(ZString.FINSET))
            word = "&Fopf;";
        else if (word.equals(ZString.POWER))
            word = "&Popf;";
        return word;
    }
    
    /**
     * Returns the word part of a DeclName ensuring it is not empty.
     */
    private String getWord(DeclName name) {
        ZDeclName dname = ZUtils.assertZDeclName(name);        
        assert dname != null && dname.getWord().length() > 0 : "A valid word can be neither null nor empty.";
        String result = dname.getWord();
        result = translateWord(result);
        return result;
    }
    
    private String getWord(RefName name) {
        ZRefName rname = ZUtils.assertZRefName(name);
        assert rname != null && rname.getWord().length() > 0 : "A valid word can be neither null nor empty.";
        String result = rname.getWord();
        result = translateWord(result);
        return result;
    }
    
    private String getWord(Term name) {
        if (name instanceof DeclName)
            return getWord((DeclName)name);
        else
            return getWord((RefName)name);
    }
    
    private String getSchExprOpName(SchExpr2 term) {
        String result;
        if (term instanceof CompExpr)
            result = "&fatsemi;";
        else if (term instanceof PipeExpr)
            result = "&gtgt";
        else if (term instanceof ProjExpr)
            result = "&uharr;";
        else if (term instanceof AndExpr)
            result = "&wedge;";
        else if (term instanceof OrExpr)
            result = "&vee;";
        else if (term instanceof ImpliesExpr)
            result = "&rArr;";
        else if (term instanceof IffExpr)
            result = "&hArr;";
        else
            throw new ZEvesIncompatibleException("binary schema expression term", term);
        return result;
    }
    
    private String getFixity(OperatorName.Fixity fixity) {
        String result;
        if (fixity == OperatorName.Fixity.PREFIX)
            result = "pre-rel";
        else if (fixity == OperatorName.Fixity.POSTFIX)
            result = "post-fun";
        else if (fixity == OperatorName.Fixity.INFIX)
            result = "in-rel";
        else // if (fixity == OperatorName.Fixity.NOFIX) or everything else.
            result = "";
        return result;
    }    
    
    private String translateOperatorWord(String word) {
        // Strip the ARG_TOK.
        //word = word.substring(word.indexOf(ZString.ARG_TOK)+ZString.ARG_TOK.length(), word.lastIndexOf(ZString.ARG_TOK));
        String result;
        // Sets
        if (word.equals(ZString.NEQ))
            result = "&neq;";        
        else if (word.equals(ZString.NOTMEM))
            result = "&notin;";        
        else if (word.equals(ZString.EMPTYSET))
            result = "&empty;";        
        else if (word.equals(ZString.SUBSETEQ))
            result = "&subeq;";        
        else if (word.equals(ZString.SUBSET))
            result = "&sub;";        
        else if (word.equals(ZString.CUP))
            result = "&cup;";        
        else if (word.equals(ZString.CAP))
            result = "&cap;";        
        else if (word.equals(ZString.BIGCUP))
            result = "&bigcup;";        
        else if (word.equals(ZString.BIGCAP))
            result = "&bigcap;"; 
        else if (word.equals(ZString.SETMINUS))
            result = "\\";
        // Relations
        else if (word.equals(ZString.REL))
            result = "&ltarr;";        
        else if (word.equals(ZString.MAPSTO))
            result = "&rtarr;";        
        else if (word.equals(ZString.CIRC))
            result = "&circ;";        
        else if (word.equals(ZString.DRES))
            result = "&vltri;";
        else if (word.equals(ZString.NDRES))
            result = "&vltrib;";
        else if (word.equals(ZString.RRES))
            result = "&vrtri;";
        else if (word.equals(ZString.NRRES))
            result = "&vrtrib;";      
        else if (word.equals(ZString.TILDE))
            result = "&suptilde;";      
//        else if (word.equals(ZString.LIMG))
//            result = "&lvparen;";      
//        else if (word.equals(ZString.RIMG))
//            result = "&rvparen;";      
        else if (word.equals(ZString.OPLUS))
            result = "&oplus;";        
        else if (word.endsWith(ZString.PLUS))// % ^+
            result = "&supplus;";                
        else if (word.endsWith(ZString.MULT))// % ^*
            result = "&supstar;";        
        // Functions
        else if (word.equals(ZString.PFUN))
            result = "&rarrb;";
        else if (word.equals(ZString.FUN))
            result = "&rarr;";
        else if (word.equals(ZString.PINJ))
            result = "&raarbtl;";
        else if (word.equals(ZString.INJ))
            result = "&rarrtl;";
        else if (word.equals(ZString.PSURJ))
            result = "&Rarrb;";
        else if (word.equals(ZString.SURJ))
            result = "&Rarr;";
        else if (word.equals(ZString.BIJ))
            result = "&Rarrtl;";
        // Natural Numbers        
        else if (word.equals(ZString.LESS))
            result = "&lt;";
        else if (word.equals(ZString.LEQ))
            result = "&leq;";
        else if (word.equals(ZString.GREATER))
            result = "&gt;";
        else if (word.equals(ZString.GEQ))
            result = "&geq;";
        else if (word.equals(ZString.FFUN))
            result = "&rarrB;";
        else if (word.equals(ZString.FINJ))
            result = "&rarrBtl;";
        // Sequences
        else if (word.equals(ZString.CAT))
            result = "&frown;";
        else if (word.equals(ZString.EXTRACT))
            result = "&uharl;";
        // Bags
//        else if (word.equals(ZString.???))//Bag count
//            result = "&sharp;";
//        else if (word.equals(ZString.???)//Bag scaling
//            result = "&otimes;";
//        else if (word.equals(ZString.???))//Bag membership
//            result = "&sqisin;";
//        else if (word.equals(ZString.???))//sub-bag
//            result = "&sqsubeq;";
//        else if (word.equals(ZString.???))//bag union
//            result = "&uplus;";
//        else if (word.equals(ZString.???))//bag difference
//            result = "&uminus;";                
        else 
            result = word;
        return result;
    }
    
    private String getOperator(OperatorName opname) {
        Iterator/*<String>*/ parts = opname.iterator();
        String result = null;
        if (fRelationalOpAppl) {
            int found = 0;
            while (parts.hasNext()) {
                String part = parts.next().toString();
                if (!part.equals(ZString.ARG)) {
                    found++;
                    result = translateOperatorWord(part);
                }
            }
            if (found != 1)
                throw new ZEvesIncompatibleException("Translation of complext operator templates is not yet supported. See throwable cause for details.",
                        new IllegalArgumentException("We only implement translation of unary or binary operator templates with one \"word\" name only. " +
                        "That is, we support mostly all toolkit operators, such as \"_ < _\", but not more complex templates with more tha one \"word\", " +
                        "such as \"_ || _ @ _ \". Check the newest version readme.txt for compatibility details."));
        } else {
            //getFixity(opname.getFixity());
        }
        assert result != null;
        return result;
    }
    
    private String getOperator(Term name) {
        if (name instanceof DeclName)
            return getOperator(ZUtils.assertZDeclName((DeclName)name).getOperatorName());
        else
            return getOperator(ZUtils.assertZRefName((RefName)name).getOperatorName());
    }
    
    /**
     * Retrieves the Schema name from a DeclName: it is just the getWord()
     * method result, as we do not consider Delta and Xi schemas nor decoration
     * for schema names here.
     * Delta and Xi schemas in CZT are RefExpr. Schema decorations in CZT are
     * DecorExpr (e.g. S_0, S', etc).
     */
    private String getSchName(DeclName schName) {
        return getWord(schName);
    }
    
    private String getSchName(RefName schName) {
        return getWord(schName);
    }
    
    /**
     * Returns a list of strokes simply concatenated as it appears.
     */
    private String getStrokes(ListTerm/*<Stroke>*/ strokes) {
        StringBuilder result = new StringBuilder("");
        for(Object o : strokes) {
            Stroke stk = (Stroke)o;
            result.append(stk.accept(this));
        }
        return result.toString();
    }
    
    private String getStrokes(Term name) {
        if (name instanceof ZDeclName)
            return getStrokes(ZUtils.assertZDeclName((DeclName)name).getStroke());
        else
            return getStrokes(ZUtils.assertZRefName((RefName)name).getStroke());
    }
    
    /**
     * Represents the ident production. It extracts the word and the decorations
     * (from strokes) from a given DeclName.
     */
    private String getIdent(Term name) {
        StringBuilder result = new StringBuilder(getWord(name));
        result.append(getStrokes(name));
        return result.toString();
    }
    
    /**
     * Represents the decl-name production. It does not yet implement operator templates
     * and just recognises Z/Eves identifiers (e.g. work with decoration).
     */
    private String getDeclName(ZDeclName dname) {
        if (dname.getOperatorName() != null)
            return getOperator(dname);
        else
            return getIdent(dname);
    }
    
    private String getRefName(ZRefName rname) {
        if (rname.getOperatorName() != null)
            return getOperator(rname);
        else
            return getIdent(rname);
    }
    
    private String getName(Term name) {
        if (name instanceof ZDeclName)
            return getDeclName(ZUtils.assertZDeclName((DeclName)name));
        else
            return getRefName(ZUtils.assertZRefName((RefName)name));
    }
    
    /**
     * Returns a comma-separated list of identifiers.
     * It represents ident-list, or event-name-list.
     */
    private String getIdentList(ListTerm/*<DeclName | RefName>*/ term) {
        assert term != null;
        if (term.isEmpty())
            throw new IllegalArgumentException("Identifier lists must have at least one declaring name");
        StringBuilder result = new StringBuilder("");
        Iterator/*<DeclName | RefName>*/ it = term.iterator();
        Term name = (Term)it.next();
        result.append(getIdent(name));
        while (it.hasNext()) {
            result.append(", ");
            name = (Term)it.next();
            result.append(getIdent(name));
        }
        return result.toString();
    }
    
    /**
     * Returns a comma-separated list of decl-name or ref-name (but not mixed).
     * It assumes the list is neither null nor empty. It is used to represent
     * various productions related to names with operators.
     */    
    private /*<T extends DeclName & RefName>*/ String getNameList(Iterator<? extends Term> it) {        
        StringBuilder result = new StringBuilder("");        
        Term name = it.next();
        result.append(getName(name));
        while (it.hasNext()) {
            result.append(", ");
            name = (Term)it.next();
            result.append(getName(name));
        }
        return result.toString();
    }
    
    /**
     * Represents a simplified version of production def-lhs.
     * It just take into account our simplified version of var-name production.
     */
    private String getDefLHS(DeclName dname) {
        // TODO: Include other forms of def-lhs production.
        return getVarName(dname);
    }
    
    /**
     * Represents a simplified version of production var-name as just ident.
     * It does not take into account operator names for now, but just
     * decorations.
     */
    private String getVarName(DeclName dname) {
        // TODO: Include other forms of var-name production.
        return getIdent(dname);
    }
    
    private String getVarName(RefName rname) {
        return getIdent(rname);
    }
    
    /**
     * Returns the string corresponding to the generic formals.
     * It extracts the generic formals from a list of DeclName putting
     * together additional brackets. If the list is empty, it simply
     * returns the empty string.
     */
    private String getGenFormals(ListTerm/*<DeclName>*/ term) {
        assert term != null;
        StringBuilder result = new StringBuilder("");
        if (!term.isEmpty()) {
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
    private String getGenActuals(ZExprList term) {
        if (term.isEmpty())
            throw new IllegalArgumentException("Invalid expression list for generic actuals");
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
    private String getPred(Pred pred) {
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
        if (isNLAndPred(pred)) {
            AndPred ap = (AndPred)pred;
            result.append(getPred(ap.getLeftPred()));
            result.append(NL_SEP);
            result.append(getPred(ap.getRightPred()));
        } else {
            result.append(getPred0(pred));
        }
        assert !result.toString().equals("");
        return result.toString();
    }
    
    private String getPred0(Pred pred) {
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
            result.append(getLabel(pred));
        String p = pred.accept(this).toString();
        result.append(p);
        return result.toString();
    }
    
    /**
     * Retrieve the Z/Eves XML for the given non-null expression, something
     * the calling method must ensure, otherwise a NullPointerException (or
     * indeed an AssertionError) is thrown . Therefore, it always return some non-empty string.
     */
    private String getExpr(Expr expr) {
        assert expr != null;
        return expr.accept(this).toString();
    }
    
    /**
     * Represents the branch production used in free-type.
     * It retrieves the var-name and expression for each branch of a free-type.
     */
    private String getBranch(Branch b) {
        String result;
        if (b.getExpr() == null)
            result = getIdent(b.getDeclName());
        else {            
            result = format(BRANCH_PATTERN, getVarName(b.getDeclName()), getExpr(b.getExpr()));
        }
        return result;
    }
    
    /**
     * Represents the decl-part production. It prefixes the result of visiting the DeclList
     * with the additional XML tag needed by Z/Eves.
     */
    private String getDeclPart(ZDeclList decls) {
        StringBuilder result = new StringBuilder("<decl-part/>");
        result.append(decls.accept(this));
        return result.toString();
    }
    
    /**
     * Retrives the axiomatic part of schemas, axiomatic and generic boxes.
     * If the predicate is null, it simply returns the empty string.
     * Otherwise, appropriate Z/Eves XML tags are added.
     */
    private String getAxiomPart(Pred pred) {
        StringBuilder result = new StringBuilder("");
        if (pred != null) {
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
    private String getProofPart(ConjPara term) {
        StringBuilder result = new StringBuilder("");
        ProofScript ps = getProofScriptAnn(term);
        if (ps != null) {
            result.append("<proof-part/>");
            result.append(ps);
        }
        return result.toString();
    }
    
    /**
     * Returns the internal Z/Eves quantifier name according to the corresponding CZT QntPred subclass.
     */
    private String getQntName(QntPred term) {
        if (term instanceof ExistsPred)
            return "&exists; ";
        else if (term instanceof Exists1Pred)
            return "&exists;&sub1; ";
        else if (term instanceof ForallPred)
            return "&forall; ";
        else
            throw new ZEvesIncompatibleException("Quantified predicate", term);
    }
    
    /**
     * Returns the internal Z/Eves predicatename according to the corresponding CZT Pred2 subclass.
     */
    private String getBinPredName(Pred2 term) {
        String result;
        if (term instanceof IffPred)
            result = "&hArr;";
        else if (term instanceof ImpliesPred)
            result = "&rArr;";
        else if (term instanceof OrPred)
            result = "&vee;";
        else if (term instanceof AndPred) {
            And op = ((AndPred)term).getAnd();
            if (op.equals(And.Wedge))
                result = "&wedge;";
            else if (op.equals(And.NL))
                throw new ZEvesIncompatibleException("AndPred with new line cannot be converted through predicate tree visiting. " +
                        "NL AndPred can only appear through the axiom-part production.");
            else
                throw new ZEvesIncompatibleException("Chain and Semi AndPred appearing in the predicate tree visiting has not yet been implemented." +
                        "Chain AndPred appears with predicates such as \"x = y = z\", which can be easily avoided.");
        } else
            throw new ZEvesIncompatibleException("Quantified predicate", term);
        return result;       
    }    
        
    /**
     * Retrieves the kind of the given MemPred.
     * It deals with the four cases available for: set containment (ex: X isin Y),
     * n-ary and unary relational operator application (X < Y, disjoint~S), and
     * equality (X = Y). It throws a ZEvesIncompatibleException when none
     * of these cases can be identified.
     */
    private MemPredKind getMemPredKind(MemPred term) {
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
        if (!term.getMixfix()) { // case 1
            result = MemPredKind.SET_MEMBERSHIP;
        } else {
            Expr right = term.getRightExpr();
            if (right instanceof RefExpr) {        // case 2.1
                Expr left = term.getLeftExpr();
                if (left instanceof TupleExpr) // case 2.1.1
                    result = MemPredKind.NARY_RELOP_APPLICATION;
                else // case 2.1.2
                    result = MemPredKind.UNARY_RELOP_APPLICATION;
            } else if (right instanceof SetExpr) { // case 2.2
                result = MemPredKind.EQUALITY;
            } else
                throw new ZEvesIncompatibleException("Invalid relational operator application, while trying to convert" +
                        "CZT membership predicate to Z/Eves XML API. See throwable cause for details.",
                        new IllegalArgumentException("In CZT (and Z standard) relational operators can appear as predicates. " +
                        "There are two cases to consider: n-ary, and unary relational operators. For n-ary operators, the " +
                        "left expression must be a TupleExpr containing all the arguments for the relational operator. For " +
                        "instance, x~\\subseteq~y is represented as (mixfix=boolean values) \n\t " +
                        "MemPred(TupleExpr(RefExpr(\"x\", false), RefExpr(\"y\", false)), RefExpr(\"_~\\subseteq~_\", false), true)\n " +
                        "On ther other hand, for unary operators, the left expression can be the actual expression being applied" +
                        "for the relational operator in question. For instance, \\disjoint~{ s, t } is represeted as \n\t " +
                        "MemPred(SetExpr(RefExpr(\"s\", false), RefExpr(\"t\", false)), RefExpr(\"\\disjoint~_\"), true)"));
        }
        return result;
    }
    
    /**
     * Returns the relational operator name for the given RefExpr, which is part of a MemPred term.
     */
    private String getMemPredRelOpName(RefExpr refexpr) {        
        fRelationalOpAppl = true;
        String result = getExpr(refexpr);
        fRelationalOpAppl = false;
        if (result == null || result.equals(""))
            throw new ZEvesIncompatibleException("Relational operator could not be translated. See throwable cause for details.",
                    new IllegalArgumentException("It wasn't possible to properly translate relational operator " +
                    refexpr.getRefName().toString() + " into Z/Eves format."));
        return result;
    }

    private Ability getDefaultAbility() {
        return Ability.none;
    }
    
    private Usage getDefaultUsage() {
        return Usage.none;
    }
            
    private Label createLabel(TermA term) {        
        String thmName = term.getClass().getSimpleName() + term.hashCode();
        Label result = new Label(thmName, getDefaultAbility(), getDefaultUsage());
        return result;
    }

    /* Top-level operations */
    
    /**
     * Top-level method which translates the given CZT term to a corresponding Z/Eves
     * server XML API. It only accepts Para, Pred, or Expr because Z/Eves adds sections
     * via a set of commands rather than a simple command.
     */
    public String print(Term term) {
        if (term == null)
            throw new NullPointerException("Cannot convert a null term to Z/Eves XML");
        if (!(term instanceof Para || term instanceof Pred || term instanceof Expr))
            throw new ZEvesIncompatibleException("This class can only print Para, Pred, and Expr terms. For other " +
                    "terms such as Spec and ZSection, one should use the ZEvesEvaluator class, as it allows appropriate " +
                    "handling of Z sections through special commands needed by the Z/Eves server.");
        return term.accept(this).toString();
    }
    
    public List<String> printSpec(Spec term, SectionInfo si) {
        setSectionInfo(si);
        return term.accept(fSpecPrinter);
    }
    
    public List<String> printSpec(ZSect term, SectionInfo si) {
        setSectionInfo(si);
        return term.accept(fSpecPrinter);
    }
    
    public String print(Term term, SectionInfo si) {
        setSectionInfo(si);  
        return print(term);
    }
    
    public void setSectionInfo(SectionInfo si) {
        fSectionInfo = si;
    }
    
    public SectionInfo getSectionInfo() {
        return fSectionInfo;
    }
    
    /* Special Terms */
    
    public String visitTerm(Term term) {
        throw new ZEvesIncompatibleException("Term", term);
    }
    
    public String visitFreetype(Freetype term) {
        if (term.getBranch().isEmpty())
            throw new IllegalArgumentException("Free type declarations must have at least one branch.");
        StringBuilder result = new StringBuilder(getIdent(term.getDeclName()));
        result.append("::=");
        Iterator/*<Branch>*/ it = term.getBranch().iterator();
        Branch b = (Branch)it.next();
        result.append(getBranch(b));
        while (it.hasNext()) {
            result.append(" | ");
            b = (Branch)it.next();
            result.append(b);
        }        
        return format(ZED_BOX_FREETYPE_PATTERN, getLocation(term), getAbility(term), result.toString());
    }
    
    public String visitSchText(SchText termx) {
        ZSchText term = ZUtils.assertZSchText(termx);
        StringBuilder result = new StringBuilder("");
        boolean needBar = false;
        if (!term.getZDeclList().isEmpty()) {
            result.append(term.getZDeclList().accept(this));
            needBar = true;
        }
        if (term.getPred() != null) {
            if (needBar)
                result.append(" | ");
            result.append(getPred(term.getPred()));
        }
        return result.toString();
    }
    
    public String visitZDeclName(ZDeclName term) {
        return getDeclName(term);
    }
    
    public String visitZRefName(ZRefName term) {
        return getRefName(term);
    }
    
    /* Special Z Lists */

    /**
     * Represents the declaration production. Firstly, it checks for empty
     * declaration incompatibility. Next, it iterates through all elements from the
     * list appending the definition for each Decl from decls.
     */
    public String visitZDeclList(ZDeclList decls) {
        /* NOTE:
         *
         * Z/Eves does not accept empty declarations, as allowed by the Z standard.
         * Therefore, we do need to restrict the CZT here with and additional check.
         */
        if (decls.isEmpty())
            emptyDeclPartException();
        StringBuilder result = new StringBuilder("");
        Iterator<Decl> it = decls.iterator();
        Decl d = it.next();
        result.append(d.accept(this));
        while (it.hasNext()) {
            result.append(NL_SEP); // sep chosen to be NL
            d = (Decl)it.next();
            result.append(d.accept(this));
        }
        return result.toString();
    }
    
    /**
     * Represents the expression-list production. It ensures first that the list
     * is not empty, and then traverse it by building up a comma-separated list
     * of expressions.
     */
    public String visitZExprList(ZExprList term) {         
        assert !term.isEmpty() && fZExprListSep != null 
                && !fZExprListSep.equals("") : "Expression list can be neither null nor empty.";
        StringBuilder result = new StringBuilder("");
        Iterator<Expr> it = term.iterator();
        Expr e = it.next();
        result.append(getExpr(e));
        while (it.hasNext()) {
            result.append(fZExprListSep);
            e = it.next();
            result.append(getExpr(e));
        }
        return result.toString();
    }
    
    public String visitZRefNameList(ZRefNameList term) {                
        return getNameList(term.iterator());
    }

    /* Z Strokes */
    
    /* NOTE:
     *
     * Z/Eves strokes are just plain text. They do not have the special
     * Z Standard symbols such as ZString.SE + ZString.NW.
     *
     */
    
    public String visitStroke(Stroke term) {
        throw new ZEvesIncompatibleException("Stroke", term);
    }
    
    public String visitNumStroke(NumStroke term) {        
        Integer i = term.getDigit();
        if (i < 0 || i > 9)
            throw new ZEvesIncompatibleException("Z/Eves only accepts number strokes from 0 up to 9 (inclusive)");        
        return format(NUM_STROKE_PATTERN, i.toString());
    }
    
    public String visitInStroke(InStroke term) {
        return "?";
    }
    
    public String visitOutStroke(OutStroke term) {
        return "!";
    }
    
    public String visitNextStroke(NextStroke term) {
        return "&apos;";
    }
    
    /* Z Paragraphs */
    
    public String visitPara(Para term) {
        throw new ZEvesIncompatibleException("Paragraph", term);
    }
    
    public String visitNarrPara(NarrPara term) {        
        return comment("Narrative Paragraph", term.getContent().toString());
    }
    
    public String visitLatexMarkupPara(LatexMarkupPara term) {        
        return comment("LaTeX Markup Directives Paragraph", term.getDirective().toString());
    }
    
    public String visitUnparsedPara(UnparsedPara term) {        
        return comment("Unparsed Paragraph", term.getContent().toString());
    }
    
    public String visitConjPara(ConjPara term) {        
        String axiomPart = getAxiomPart(term.getPred());
        if (axiomPart.equals("")) {
            throw new ZEvesIncompatibleException("Z/Eves conjectures must not have an empty predicate part.");
        }
        Label l = getLabelAnn(term);
        if (l == null) {
            l = createLabel(term);
            term.getAnns().add(l);                        
        }            
        String result = format(THEOREM_DEF_PATTERN, getLocation(term), l.getAbility(), l.getUsage(),
                l.getTheoremName(), NL_SEP + getGenFormals(term.getDeclName()),
                axiomPart, getProofPart(term));
        return wrapPara(result);
    }
    
    public String visitGivenPara(GivenPara term) {        
        String result = format(ZED_BOX_GIVENSET_PATTERN, 
                getLocation(term), getAbility(term), getIdentList(term.getDeclName()));
        return wrapPara(result);
    }
    
    public String visitAxPara(AxPara term) {
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
        String genFormals = getGenFormals(term.getDeclName());
        assert genFormals != null;
        if (b.equals(Box.SchBox)) {
            assert term.getZSchText().getPred() == null;
            ConstDecl cd = (ConstDecl)term.getZSchText().getZDeclList().get(0);
            DeclName schName = cd.getDeclName();
            ZSchText schText = ((SchExpr)cd.getExpr()).getZSchText();
            
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
            if (!isPredicatePara(schText)) {
                decls = getDeclPart(schText.getZDeclList());                
                result = format(SCHEMA_BOX_PATTERN, getLocation(term), 
                        getAbility(term), getSchName(schName), NL_SEP + genFormals, decls, preds);
            } else {
                if (preds == null || preds.equals(""))
                    throw new ZEvesIncompatibleException("Schema boxes without declaration must have the predicate part to be considered a Z/Eves predicate paragraph.");                
                result = format(PREDICATE_PARA_PATTERN, getLocation(term), getAbility(term), preds);
            }
        } else if (b.equals(Box.AxBox)) {
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
            if (!isPredicatePara(term.getSchText())) {
                decls = getDeclPart(term.getZSchText().getZDeclList());
                if (genFormals.equals("")) {                    
                    result = format(AXIOMATIC_BOX_PATTERN,
                            getLocation(term), getAbility(term), decls, preds);
                } else {                    
                    result = format(GENERIC_BOX_PATTERN, getLocation(term), getAbility(term), genFormals, decls, preds);
                }
            } else {
                if (preds == null || preds.equals(""))
                    throw new ZEvesIncompatibleException("Axiomatic boxes without declaration must have the predicate part to be considered a Z/Eves predicate paragraph.");                
                result = format(PREDICATE_PARA_PATTERN, getLocation(term), getAbility(term), preds);
            }
        } else if (b.equals(Box.OmitBox)) {
            assert term.getZSchText().getPred() == null;
            ConstDecl cd = (ConstDecl)term.getZSchText().getZDeclList().get(0);
            DeclName hdefName = cd.getDeclName();
            Expr expr = cd.getExpr();
            String zboxItemName = (expr instanceof SchExpr) ? getSchName(hdefName) : getDefLHS(hdefName);
            String zboxItemSymbol = (expr instanceof SchExpr) ? "&eqhat;" : "==";
            String zboxItemExpr = getExpr(expr);            
            result = format(ZED_BOX_HORIZONTAL_PATTERN, getLocation(term), getAbility(term), zboxItemName,
                    genFormals, zboxItemSymbol, zboxItemExpr);
        } else {
            throw new IllegalArgumentException("Invalid box parameter for AxPara");
        }
        return wrapPara(result);
    }
    
    public String visitFreePara(FreePara term) {
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
        for(Object o : term.getFreetype()) {
            Freetype ft = (Freetype)o;
            
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
    
    public String visitDecl(Decl term) {
        throw new ZEvesIncompatibleException("Declaration", term);
    }
    
    public String visitInclDecl(InclDecl term) {
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
            throw new ZEvesIncompatibleException("Z/Eves restricts the kinds of expressions that can be used " +
                    "in inclusion declarations. The expression present on the current inclusion could not be " +
                    "translated. Please look at the throwable cause for further details.", cause);
        return "";
    }
    
    /* NOTE:
     *
     * CZT ConstDecl cannot appear for Z/Eves.
     * In CZT It only appears during definition of paragraphs, which are
     * treated specially and separetely without visiting ConstDecl.
     * Therefore, we leave it to be caught by the generic Decl as an error.
     *
    public String visitConstDecl(ConstDecl term) {
        return term;
    }
     */
    public String visitVarDecl(VarDecl term) {
        if (term.getDeclName().isEmpty())
            throw new IllegalArgumentException("Empty basic declaration list (at CZT VarDecl) is not allowed.");
        if (term.getExpr() == null)
            throw new IllegalArgumentException("Empty basic declaration expression (at CZT VarDecl) is not allowed.");
        /* NOTE:
         *
         * This visitor represent parts of basic-decl, precisely,
         * decl-name-list : expr
         */
        StringBuilder result = new StringBuilder(getNameList(term.getDeclName().iterator()));
        result.append(": ");
        result.append(getExpr(term.getExpr()));
        return result.toString();
    }
    
    /* Z Predicates */
    
    public String visitPred(Pred term) {
        throw new ZEvesIncompatibleException("Predicate", term);
    }
    
    public String visitTruePred(TruePred term) {
        return "true";
    }
    
    public String visitFalsePred(FalsePred term) {
        return "false";
    }
    
    public String visitNegPred(NegPred term) {                        
        return format(NEG_PRED_PATTERN, getPred(term.getPred()));
    }
    
    public String visitQntPred(QntPred term) {
        /* NOTE: This case covers quatifiers Exists, Exists1, and Forall.
         */        
        return format(QNT_PRED_PATTERN, getQntName(term), term.getSchText().accept(this).toString(), getPred(term.getPred()));
    }
    
    public String visitPred2(Pred2 term) {
        /* NOTE: This case covers predicates iff, implies, and, or.
         */        
        return format(BIN_PRED_PATTERN, getPred(term.getLeftPred()), getBinPredName(term), getPred(term.getRightPred()));
    }
    
    public String visitMemPred(MemPred term) {
        /* NOTE: This case covers isin, and relational operators (n-ary, unary, and =).
         */        
        MemPredKind kind = getMemPredKind(term);
        String rel, left, right;        
        switch (kind) {
            case SET_MEMBERSHIP:
                left = getExpr(term.getLeftExpr());
                rel = "&isin;";                
                right = getExpr(term.getRightExpr());
                break;
            case NARY_RELOP_APPLICATION:
                ZExprList params = ((TupleExpr)term.getLeftExpr()).getZExprList();
                assert !params.isEmpty();
                if (params.size() != 2)
                    throw new ZEvesIncompatibleException("Current version only supports translation of binary relational operators.");
                left = getExpr(params.get(0));
                rel = getMemPredRelOpName((RefExpr)term.getRightExpr());                
                right = getExpr(params.get(1));
                break;
            case UNARY_RELOP_APPLICATION:
                RefExpr refexpr = (RefExpr)term.getRightExpr();
                OperatorName.Fixity fixity = refexpr.getZRefName().getOperatorName().getFixity();
                rel = getMemPredRelOpName(refexpr);
                /* NOTE:
                 * The actual unary parameter comes from the left expression and is placed according to the fixture.
                 */
                if (fixity == OperatorName.Fixity.PREFIX) {
                    // Prefix: left+rel+right = ""+rel+right
                    left = "";
                    right = getExpr(term.getLeftExpr());
                } else if (fixity == OperatorName.Fixity.POSTFIX) {
                    // Postfix: left+rel+right = left+rel+""
                    left = getExpr(term.getLeftExpr());
                    right = "";                    
                } else 
                    throw new ZEvesIncompatibleException("Unsupported fixture for relational operator (" + fixity.toString() + ").");                
                break;
            case EQUALITY:
                /* NOTE: 
                 *
                 * For equality, the left expression is a Expr, whereas the 
                 * right expression must be a SetExpr containing only one element 
                 */                
                left = getExpr(term.getLeftExpr());
                rel = " = ";
                right = getExpr((Expr)((SetExpr)term.getRightExpr()).getZExprList().get(0));        
                break;
            default:
                throw new AssertionError("Invalid MemPredKind " + kind);
        }
        String result = format(MEMPRED_PATTERN, left, rel, right);
        assert result != null && !result.equals("");
        return result;
    }
    
    public String visitExprPred(ExprPred term) {
        /* NOTE: This case covers schema-ref, refexpr, schema precondition, conditional, and let.
         */
        return getExpr(term.getExpr());
    }
    
    /* NOTE: Dealt with directly through visitPred2. The case with NL is not
     *       allowed here. It can only appear for axiom-part instead, and is
     *       dealt with by getAxiomPart directly. The need for this is due to
     *       our design decision to include labelled-predicate whilst translating.
     *
    public String visitAndPred(AndPred term) {
    }
     */
    
    /* Z Expressions */
    public String visitExpr(Expr term) {
        throw new ZEvesIncompatibleException("Expression", term);
    }
    
    public String visitPowerExpr(PowerExpr term) {
        return format(POWER_EXPR_PATTERN, getExpr(term.getExpr()));
    }
    
    public String visitRefExpr(RefExpr term) {
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
            throw new ZEvesIncompatibleException("CZT RefExpr generic operator application translation to Z/Eves is not yet implemented " +
                    "(for \"" + term.getRefName().toString() + "\").");
        // others are more straightforward.
        else {
            String genActuals = "";
            if (!term.getZExprList().isEmpty()) {
                genActuals = getGenActuals(term.getZExprList());
            }
            // TODO: Check names for appropriate translation.
            result = getRefName(term.getZRefName()) + genActuals;
            // TODO: Detal with replacements! Not yet implemented?
        }
        assert result != null && !result.equals("");
        return result;
    }
    
    public String visitNegExpr(NegExpr term) {        
        return format(NEG_EXPR_PATTERN, getExpr(term.getExpr()));
    }
    
    public String visitMuExpr(MuExpr term) {
        String schText = term.getSchText().accept(this).toString();
        String expr = "";
        if (term.getExpr() != null)
            expr = "&bullet; " + getExpr(term.getExpr());
        return "&mu; " + schText + expr;
    }
    
    public String visitLambdaExpr(LambdaExpr term) {        
        return format(LAMBDA_EXPR_PATTERN, "&lambda;", 
                term.getSchText().accept(this).toString(), getExpr(term.getExpr()));
    }
    
    public String visitLetExpr(LetExpr term) {
        throw new ZEvesIncompatibleException("CZT Let expression/predicate term " +
                "contains a SchText where Z/Eves expects a led-def production. " +
                "This translation is complex and requires effort not yet implemented " +
                "in this version, sorry.");        
        //return format(LET_EXPR_PATTERN, getLetDef(term.getSchText()), getExpr(term.getExpr()));
    }
    
    public String visitTupleSelExpr(TupleSelExpr term) {        
        return format(TUPLESEL_EXPR_PATTERN, getExpr(term.getExpr()), term.getNumeral().toString());
    }
    
    public String visitPreExpr(PreExpr term) {        
        return format(PRE_EXPR_PATTERN, getExpr(term.getExpr()));
    }
    
    public String visitSetExpr(SetExpr term) {        
        StringBuilder sb = new StringBuilder("{ ");        
        if (!term.getZExprList().isEmpty()) {
            fZExprListSep = ", ";
            sb.append(term.getZExprList().accept(this));
        }
        sb.append(" }");
        return sb.toString();
    }
    
    public String visitNumExpr(NumExpr term) {
        return term.getValue().toString();
    }
    
    public String visitCondExpr(CondExpr term) {        
        return format(COND_EXPR_PATTERN, getPred(term.getPred()), 
                getExpr(term.getLeftExpr()), getExpr(term.getRightExpr()));
    }
    
    public String visitProdExpr(ProdExpr term) {
        fZExprListSep = "&cross; ";
        return "(" + term.getZExprList().accept(this) + ")";
    }
    
    public String visitTupleExpr(TupleExpr term) {
        fZExprListSep = ", ";
        return "(" + term.getZExprList().accept(this) + ")";
    }
    
    public String visitBindExpr(BindExpr term) {        
//        assert !term.getNameExprPair().isEmpty() : "Binding expression list cannot be empty.";
//        StringBuilder result = new StringBuilder("&lvang; ");
//        term.getDecl()
//        ((ZDeclList)term.getDeclList()).getDecl()
//        Iterator/*<NameExprPair>*/ it = term.getNameExprPair().iterator();
//        NameExprPair nep = (NameExprPair)it.next();        
//        result.append(getBinding(nep));
//        while (it.hasNext()) {
//            result.append(";");
//            nep = (NameExprPair)it.next();
//            result.append(getBinding(nep));
//        }
//        result.append(" &rvang;");
//        return result.toString();
        throw new UnsupportedOperationException("Bind expressions are not yet supported for conversion. TODO.");
    }
    
    public String visitBindSelExpr(BindSelExpr term) {
        if (!(term.getExpr() instanceof RefExpr))
            throw new ZEvesIncompatibleException("Z/Eves only allows bind selection for schema references, " +
                    "rather than schema expressions. See throwable cause for details.",
                    new IllegalArgumentException("Invalid schema expression binding selection for Z/Eves XML translation. CZT and" +
                    "the Z Standard allow bind selection upon schema expressions, such as (S \\land T).x or (\\theta S).x." +
                    "On the other hand, Z/Eves only accepts bind selection upon schema-ref, which must be a reference name to a " +
                    "previously declared schema. The solution for this is simple: rewrite the specification so that these references " +
                    "do not appear. TODO: In a later version, we plan to automatically include such declarations implicitly, while " +
                    "translating the binding selection itself. Check whether a new version with such feature is available."));        
        return format(BINDSEL_EXPR_PATTERN, getExpr((RefExpr)term.getExpr()), getVarName(term.getZRefName()));
    }
    
    public String visitThetaExpr(ThetaExpr term) {
        Expr e = term.getExpr();
        if (!(e instanceof RefExpr || e instanceof DecorExpr || e instanceof RenameExpr))
            throw new ZEvesIncompatibleException("Z/Eves only allows theta expressions to schema references, " +
                    "rather than schema expressions. See throwable cause for details.",
                    new IllegalArgumentException("Invalid theta expression for Z/Eves XML translation. CZT and" +
                    "the Z Standard allow theta expressions of schema expressions, such as \\theta(S \\land T)." +
                    "On the other hand, Z/Eves only accepts theta expressions of schema-ref, which must be a reference name to a " +
                    "previously declared schema. The solution for this is simple: rewrite the specification so that these references " +
                    "do not appear. Some examples where there dependencies on the values (e.g. Circcus Operational Semantics) this is " +
                    "not possible to naively translate and need to be rewritten, tough. TODO: In a later version, we plan to automatically " +
                    "include such declarations implicitly whenever possible, while translating the binding selection itself. " +
                    "Check whether a new version with such feature is available."));        
        return format(THETA_EXPR_PATTERN, getExpr(term.getExpr()));
    }
    
    public String visitSchExpr2(SchExpr2 term) {
        /* NOTE: 
         * This production covers: CompExpr, PipeExpr, ProjExpr, AndExpr, 
         * OrExpr, ImpliesExpr, and IffExpr.
         */         
        return format(BIN_SCHEXPR_PATTERN, term.getLeftExpr(), getSchExprOpName(term), term.getRightExpr());
    }

    public String visitSchExpr(SchExpr term) {
        // TODO: Check whether this is ok or not.
        return term.getSchText().accept(this).toString();
    }

    public String visitHideExpr(HideExpr term) {                        
        return format(HIDE_EXPR_PATTERN, getExpr(term.getExpr()), term.getZRefNameList().accept(this));
    }    
    
//    public String visitApplExpr(ApplExpr term) {
//        
//    }
//    
    /* Main Z terms */
    
    /**
     * {0} string       => term.getName();
     * {1} parents list => getParents(term.getParent());
     * {2} paragraphs   => getParas(term.getPara());
     */ 
    private static final String ZSECTION_BEGIN_PATTERN = "<cmd name=\"begin-section\"> {0} '{'{1}'}' </cmd>";
    private static final String ZSECTION_END_PATTERN = "<cmd name=\"end-section\"/></cmd>";
    
    /**
     * Z/Eves toolkit overrides CZT toolkits.
     */
    private static final String ZEVES_TOOLKIT_NAME = "toolkit";
    private static final String[] Z_TOOLKIT_NAMES = { "prelude", "number_toolkit", 
            "set_toolkit", "relation_toolkit", "function_toolkit", 
            "sequence_toolkit", "standard_toolkit"};
    private static final List<String> sZToolkits = new ArrayList<String>(Arrays.asList(Z_TOOLKIT_NAMES));    
   
    /**
     * Special visitor class to translate top-level Z terms. 
     * Each element in the returned list must be transmitted to the Z/Eves
     * server separately, in the given order.
     */
    private class SpecPrinter implements 
            TermVisitor<List<String>>,
            SpecVisitor<List<String>>, 
            ZSectVisitor<List<String>> {

        /**
         * Returns a comma-separated list of toolkit names, where standard Z toolkit names are not 
         * included as they are loaded in Z/Eves by default. Moreover, user sections must NOT be
         * named "toolkit" as this is a reserved name for Z/Eves.
         */
        private String getParents(List<Parent> parents) {        
            StringBuilder sb = new StringBuilder(ZEVES_TOOLKIT_NAME);
            Iterator<Parent> it = parents.iterator();
            while (it.hasNext()) {
                Parent p = it.next();
                String sect = p.getWord();
                if (sect.equals(ZEVES_TOOLKIT_NAME))
                    throw new ZEvesIncompatibleException("\"toolkit\" is a reserved section name for Z/Eves use only.");
                // Include only user defined toolkits, rather than the standard ones.
                if (!sZToolkits.contains(sect)) {                
                    sb.append(", ");
                    sb.append(p.getWord());                
                }
            }         
            return sb.toString();
        }

        /**
         * Throws an exception for unexpected items.
         */
        public List<String> visitTerm(Term term) {
            throw new ZEvesIncompatibleException("term", term);
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
        public List<String> visitZSect(ZSect term) {
            List<String> result = new ArrayList<String>();
            result.add(format(ZSECTION_BEGIN_PATTERN, term.getName(), 
                    getParents(term.getParent())));
            for(Para p : term.getPara()) {
                result.add(p.accept(CZT2ZEvesPrinter.this));
            }
            result.add(ZSECTION_END_PATTERN);
            return result;
        }

        /**
         * Translates the all sections within this specification following
         * the protocol for ZSect terms.
         * At the head of the returned list we include a comment containing
         * the inforemation for the specification header.
         */
        public List<String> visitSpec(Spec term) {
            List<String> result = new ArrayList<String>();
            result.add(comment("Specification Information", 
                    String.valueOf(term.getAuthor()) + "\t\n" + 
                    String.valueOf(term.getVersion()) + "\t\n" + 
                    String.valueOf(term.getModified()) + "\t\n" + 
                    String.valueOf(term.getSource())));            
            for(Sect sect : term.getSect()) {
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

