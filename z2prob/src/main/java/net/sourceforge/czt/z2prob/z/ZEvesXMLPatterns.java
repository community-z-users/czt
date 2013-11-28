/*
 * ZEvesXMLPatterns.java
 *
 * Created on 29 November 2005, 16:27
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.zeves.z;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 *
 * @author leo
 */
public interface ZEvesXMLPatterns {
    /**
     * VARIOUS STRINGS USED AS Z/EVES XML PATTERNS FOR FORMATTING OPERATIONS
     */
    
    public static final String SC_SEP = ";";
    public static final String EQ_SIGN = " = ";
    public static final String NL_SEP = System.getProperty("line.separator");    
    
    /**
     * Main XML API command for Z/EVES. DO NOT INCLUDE NL before/after {1}.
     */
    public static final String ZEVES_COMMAND = "<cmd name=\"{0}\">{1}</cmd>";
    
    public static final String COMMENT_PATTERN = "<!-- \n *** {0} *** \n\n {1} \n-->";

    /* Operator templates */
    public static final String OPERATOR_TEMPLATE_COMMENT = "{0} {1} {2} ({3})";
    public static final String OEPRATOR_TEMPLATE_PATTERN = "<syntax-def>{0} {1} {2}</syntax-def>";
    public static final String LATEX_MARKUP_DIRECTIVE_COMMENT = "{0} {1} {2}";

    public static final String ZEVES_PROOF_PART_PATTERN = "<proof-part/> {0}";


    /* Main Z terms */
    /**
     * {0} string       => term.getName();
     * {1} parents list => getParents(term.getParent());
     * {2} paragraphs   => getParas(term.getPara());
     */
    public static final String ZSECTION_BEGIN_PATTERN = "<cmd name=\"begin-section\"> {0} {1} </cmd>";
    public static final String ZSECTION_END_PATTERN = "<cmd name=\"end-section\"/></cmd>";
    /**
     * Z/EVES toolkit overrides CZT toolkits.
     */
    public static final String ZEVES_TOOLKIT_NAME = "toolkit";
    public static final List<String> Z_TOOLKIT_NAMES = Collections.unmodifiableList(Arrays.asList(
            "prelude", "number_toolkit", "set_toolkit", "relation_toolkit", "function_toolkit",
            "sequence_toolkit", "standard_toolkit"));

    /* Special XML pattern strings */
    
    /**
     * {0} = number     => term.getNumber().toString()
     */
    public static final String NUM_STROKE_PATTERN = "&sub{0};";
    
    /**
     * {0} = var-name   => getVarName(term.getZName());
     * {1} = expr       => getExpr(term.getExpr());
     */
    public static final String BRANCH_PATTERN = "{0} &lchev; {1} &rchev;";
    
    /* z-paragraph XML pattern strings */
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = zboxItemName    => getSchName(((ConstDecl)term.getZSchText().getZDeclList()).getZName()); |
     *                          getDefLHS(((ConstDecl)term.getZSchText().getZDeclList()).getZName());
     * {3} = gen-formals     => getGenFormals(term.getZName());
     * {4} = zboxItemSymbol  => "&eqhat;" | "=="
     * {5} = zboxItemExpr    => getExpr(((ConstDecl)term.getZSchText().getZDeclList()).getExpr());
     *
     * For postix, genformals appear early. For prefix, we have a different production with an extra parameter
     */
    public static final String ZED_BOX_HORIZONTAL_PATTERN = "<zed-box {0} {1}>{2} {3} {4} {5}</zed-box>";
    public static final String ZED_BOX_INFIXGENOP_HORIZONTAL_PATTERN = "<zed-box {0} {1}>{2} {3} {4} {5} {6}</zed-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = zboxItemNameList=> getIdentList(term.getZNames());
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
     * {2} = generic formals => getGenFormals(term.getZName());
     * {3} = decl-part       => getDeclPart(term.getZSchText().getZDeclList());
     * {4} = axiom-part      => getAxiomPart(term.getSchText().getPred());
     */
    public static final String GENERIC_BOX_PATTERN = "<generic-box {0} {1}>{2} {3} {4}</generic-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = schema-name     => getSchName(((ConstDecl)term.getZSchText().getZDeclList()).getZName());
     * {3} = generic formals => NL_SEP + getGenFormals(term.getZName());
     * {4} = decl-part       => getDeclPart(((SchExpr)((ConstDecl)term.getZSchText().getZDeclList()).getExpr()).getZSchText().getZDeclList());
     * {5} = axiom-part      => getAxiomPart(((SchExpr)((ConstDecl)term.getZSchText().getZDeclList()).getExpr()).getSchText().getPred());
     */
    public static final String SCHEMA_BOX_PATTERN = "<schema-box {0} {1}>{2}{3}\n{4}\n{5}\n</schema-box>";
    
    /**
     * {0} = location        => getLocation(term);
     * {1} = ability         => getAbility(term);
     * {2} = usage           => getUsage(term);
     * {3} = theorem-name    => getTheoremName(term);
     * {4} = generic formals => NL_SEP + getGenFormals(term.getZName());
     * {5} = axiom-part      => getAxiomPart(term.getPred());
     * {6} = proof-part      => getProofPart(term);
     *
     * Note: Provided axiom-part is not empty.
     */
    public static final String THEOREM_DEF_PATTERN = "<theorem-def {0} {1} {2} >{3} {4}\n{5}\n{6}\n</theorem-def>";
    
    /**
     * {0} = ability      => label.getAbility();
     * {1} = usage        => label.getUsage();
     * {2} = theorem-name => label.getTheoremName();
     */
    public static final String LABEL_PATTERN = "&lchev; {0} {1} {2} &rchev;";
    
    /**
     * {0} = Line         => locAnn.getLine();
     * {1} = Column       => locAnn.getCol();
     * {2} = Start-offset => locAnn.getStart();
     * {3} = End-offset   => locAnn.getEnd();
     * {4} = lenGth       => locAnn.getLength();
     * {5} = sourCe       => locAnn.getLoc();
     */
    public static final String LOCATION_PATTERN = "location=\"L{0};C{1};S{2};E{3};G{4};R{5}\"";
    
    /**
     * {0} = Ability => label.getAbility();
     */
    public static final String ABILITY_PATTERN = "ability=\"{0}\"";
    
    /**
     * {0} = Usage => label.getUsage();
     */
    public static final String USAGE_PATTERN = "usage=\"{0}\"";

    /* predicate, predicate-1 XML pattern strings */
    
    /**
     * {0} = predicate      => getPred(term.getPred());
     */
    public static final String NEG_PRED_PATTERN = "&not; ({0})";
    
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
     *       labelled-predicates (i.e. each element on an AndPred having a Z/EVES label).
     *       For this case, we can only accept term.getOp() as And, Chain, or Semi,
     *       but not NL.
     */
    public static final String BIN_PRED_PATTERN = "({0}) {1} ({2})";
    
    /**
     * {0} expression   => getExpr(term.getLeftExpr());
     * {1} rel          => getRel(term); = "&isin;" | getRelOp(term) | "="
     * {2} expression   => getExpr(term.getRightExpr());
     *
     * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
     */
    public static final String MEMPRED_PATTERN = "{0} {1} {2}";
    
    /* expression[-n] XML productions */
    
    /**
     * {0} expression       => getExpr(term.getExpr());
     */
    public static final String NEG_EXPR_PATTERN = "&neg; ({0})";
    public static final String LAMBDA_EXPR_PATTERN = "(" + QNT_PRED_PATTERN + ")";
    public static final String QNT_EXPR_PATTERN = "(" + QNT_PRED_PATTERN + ")";
    
    /**
     * {0} let-def          => getLetDef(term.getSchText());
     * {1} expression       => getExpr(term.getExpr());
     */
    public static final String LET_EXPR_PATTERN = "(<word style=\"bold\"/>let<word/>{0} &bullet; {1})";
    
    /**
     * {0} expression       => getExpr(term.getExpr());
     *
     * NOTE: For Z/EVES this is a schema-ref, which here is simply a RefExpr.
     *       Nevertheless, care needs to be taken because in the translation of
     *       RefExpr as Z/EVES does not allow all forms of schema-expression that CZT allows.
     */
    public static final String PRE_EXPR_PATTERN = "<word style=\"roman\"/>pre<word/>{0}";
    
    public static final String ROMAN_PATTERN = "<word style=\"roman\"/>{0}<word/>";

    public static final List<String> ROMAN_NAMES = Collections.unmodifiableList(
          Arrays.asList("div", "mod", "pre", "dom", "ran", "id", "seq", "iseq", "prefix",
          "suffix", "inseq", "disjoint", "partition", "bag", "inbag"));

    
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
     * {1} strokes          => getStrokes(term.getZStrokeList());
     *
     * NOTE: The expression can represent either a schema-ref dealt with through
     *       RefExpr or DecorExpr, or schema-ref replacements dealt with through
     *       a RenameExpr.
     */
    public static final String THETA_EXPR_PATTERN = "&theta; {0} {1}";
    
    /**
     * {0} expression   => getExpr(term.getExpr());
     *
     * NOTE: For Z/EVES XML, CZT PowerExpr is just a special kind of var-name
     *       within expression-3, as there is no specific production for it.
     */
    public static final String POWER_EXPR_PATTERN = "&Popf; ({0})";
    
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
     * {1} name list    => getZNameList.accept(this);
     */
    public static final String HIDE_EXPR_PATTERN = "{0} \\ ({1})";    

    /**
     * {0} expression       => getExpr(term.getLeftExpr());
     * {1} expression       => getExpr(term.getRightExpr());
     *
     * NOTE: Added parentheses on the argument, because it may bind stronger than the expression.
     *       Also addded parentheses to the function, because it may be a complex expression
     */
    public static final String APPL_EXPR_PATTERN = "{0} {1}";
    public static final String EQ_SUBST_APPL_EXPR_PATTERN = "{0}{1}";
    public static final String UNARY_MINUS_EXPR_PATTERN = "{0}{1}";
    
    /**
     * {0} expression       => getExpr(term.getLeftExpr());
     * {1} expression       => getExpr(term.getRightExpr());
     * 
     * NOTE: No parenthesis for the postfix operator. For example, tilde symbol (inverse) 
     * needs to be without parentheses, otherwise Z/EVES throws an error.
     */
    public static final String POSTFIX_APPL_EXPR_PATTERN = "{1} {0}";
    
    // PS: the way operator templates are handled can be slightly different
    //     because of special cases like LANGLE, LIMG, etc. So, the pattern
    //     is a bit different (eg., see visitApplExpr)
    /**
     * {1} expression   => getExpr(ZUtils.getApplExprArguments(term).get(0));
     * {0} rel          => getExpr(ZUtils.getApplExprRef(term));
     * {2} expression   => getExpr(ZUtils.getApplExprArguments(term).get(1));
     *
     */
    public static final String INFIX_APPL_EXPR_PATTERN = "{1} {0} {2}";
    public static final String UNARY_MINUS_PLUS_INFIX_APPL_EXPR_PATTERN = "({1} {0} {2})";

    /**
     * {0} comma sep list of expressions from getExpr(ZUtils.getApplExprArguments(term).get(n));
     */
    public static final String APPL_EXPR_SEQ_PATTERN = "(&lang; {0} &rang;)";
    public static final String APPL_EXPR_BAG_PATTERN = "(&lbag; {0} &rbag;)";

    /**
     * {0} expression   => getExpr(ZUtils.getApplExprArguments(term).get(0));
     * {1} expression   => getExpr(ZUtils.getApplExprArguments(term).get(1));
     */
    public static final String MIXFIX_APPL_EXPR_RELIMAGE_PATTERN = "({0} &lvparen; {1} &rvparen;)";


    /**
     * {0} expression   => getExpr(term.getZExprList().get(0));
     * {1} rel          => getName(term.getZName()); 
     * {2} expression   => getExpr(term.getZExprList().get(1));
     *
     */
    public static final String INFIX_REF_EXPR_PATTERN = "(({0}) {1} ({2}))";
    
    /**
     * {0} rel          => getName(term.getZName()); 
     * {1} expression   => getExpr(term.getZExprList().get(0));
     */
    public static final String PREFIX_REF_EXPR_PATTERN = "{0} ({1})";
    public static final String POSTFIX_REF_EXPR_PATTERN = "({0}) {1}";

    /**
     * {0} semi-colon sep list of bindings as  NAME : EXPR ; NAME : EXPR ...
     */
    public static final String BIND_EXPR_PATTERN = "&lvang; {0} &rvang;";
    
    /**
     * {0} = expr         => getExpr(term.getExpr());
     * {1} = rename list  => getExpr(term.getExpr());
     */
    public static final String RENAME_EXPR_PATTERN = "{0} [ {1} ]";

}
