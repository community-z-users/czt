/*
 * ZEvesXMLPatterns.java
 *
 * Created on 29 November 2005, 16:27
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.zeves.util;

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
     * Main XML API command for Z/Eves. DO NOT INCLUDE NL before/after {1}.
     */
    public static final String ZEVES_COMMAND = "<cmd name=\"{0}\">{1}</cmd>";
    
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
    public static final String SCHEMA_BOX_PATTERN = "<schema-box {0} {1}>{2}{3}\n{4}\n{5}\n</schema-box>";
    
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
}
