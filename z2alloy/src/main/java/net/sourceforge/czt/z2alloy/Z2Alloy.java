/**
Copyright (C) 2008, 2009 Petra Malik, Clare Lenihan
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.z2alloy;

import static net.sourceforge.czt.z2alloy.ast.Sig.SEQIDX;
import static net.sourceforge.czt.z2alloy.ast.Sig.SIGINT;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.PowerTypeVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z.visitor.ProdTypeVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchemaTypeVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.TypeAnnVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;
import net.sourceforge.czt.z2alloy.ast.ExprUnary;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.Module;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;
import net.sourceforge.czt.z2alloy.ast.SubsetSig;
import net.sourceforge.czt.z2alloy.ast.Toolkit;
import net.sourceforge.czt.z2alloy.visitors.ExistsExprVisitorImpl;
import net.sourceforge.czt.z2alloy.visitors.ExprVisitorImpl;
import net.sourceforge.czt.z2alloy.visitors.FreetypeVisitorImpl;
import net.sourceforge.czt.z2alloy.visitors.PredVisitorImpl;
import net.sourceforge.czt.z2alloy.visitors.SchExprVisitorImpl;
import net.sourceforge.czt.z2alloy.visitors.ZDeclListVisitorImpl;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.visitor.RuleVisitor;

public class Z2Alloy implements TermVisitor<AlloyExpr>,
AxParaVisitor<AlloyExpr>,
ConstDeclVisitor<AlloyExpr>,
ExprVisitor<AlloyExpr>,
FreeParaVisitor<AlloyExpr>,
GivenParaVisitor<AlloyExpr>,
GivenTypeVisitor<AlloyExpr>,
InclDeclVisitor<AlloyExpr>,
LatexMarkupParaVisitor<AlloyExpr>,
NarrParaVisitor<AlloyExpr>,
OptempParaVisitor<AlloyExpr>,
PowerTypeVisitor<AlloyExpr>,
PredVisitor<AlloyExpr>,
ProdTypeVisitor<AlloyExpr>,
RuleVisitor<AlloyExpr>,
SchemaTypeVisitor<AlloyExpr>,
TypeAnnVisitor<AlloyExpr>,
VarDeclVisitor<AlloyExpr>,
ZSectVisitor<AlloyExpr>
{
  private final SectionManager manager_;
  private final AlloyPrintVisitor printVisitor_ = new AlloyPrintVisitor();
  private final String section_ = "z2alloy";
  private boolean unfolding_ = false;

  // this is public only temporarily 
  public boolean body = false;

  private final Module module_ = new Module();
  private final RelationMap relationMap_ = new RelationMap(module_);
  private final Map<String, AlloyExpr> macros_ = new HashMap<String, AlloyExpr>();

  /**
   * A mapping from ZName ids to alloy names.
   */
  private final Map<Expr, String> names = new HashMap<Expr, String>();

  private final Map<String, String> names_ = new HashMap<String, String>();

  /* this is a somewhat clumsy singleton pattern - its clumsy because I need
   * the SectionManager argument for the instantiation
   */
  private static Z2Alloy instance;

  public static Z2Alloy getInstance() {
    return instance;
  }

  public static Z2Alloy setInstance(SectionManager manager) throws Exception {
    return new Z2Alloy(manager);
  }

  private Z2Alloy(SectionManager manager) throws Exception {
    manager_ = manager;
    module_.addModule(new Toolkit());
    instance = this;
  }

  public void setUnfolding(boolean unfolding) {
    unfolding_ = unfolding;
  }

  public Module module() {
    return module_;
  }
  
  public Map<Expr, String> names() {
    return names;
  }
  
  public Map<String, AlloyExpr> macros() {
    return macros_;
  }
  
  public AlloyPrintVisitor printVisitor() {
    return printVisitor_;
  }
  
  public RelationMap relationMap() {
    return relationMap_;
  }

  // ==================== Visitor Methods ==================

  @Override
public AlloyExpr visitTerm(Term term) {
    System.err.println(term.getClass() + " not yet implemented");
    throw new RuntimeException(print(term));
  }

  /**
   * If the para is a schema defined by a schema expression, it creates a new
   * signiture which contains all the fields of the translated sigs of the
   * schemas in the expression. The precicate of the new sig is the result of
   * recursively calling visit on the schema expression, ie the expression
   * created by visitAndExpr, visitOrExpr, etc.
   * 
   * eg for
   * 
   * <pre>
   *    A =&gt; sig A {a : univ}{pred_A[a]} pred pred_A[a:univ]{...}
   *    B =&gt; sig B {b : univ}{pred_B[b]} pred pred_B[b:univ]{...}
   *    C =&gt; sig C {c : univ}{pred_C[c]} pred pred_C[c:univ]{...}
   *  
   *    D == (A \land B) \lor C
   *    
   *  =&gt;
   *    sig D {a : univ, b : univ, c : univ}{pred_D[a,b,b]} pred pred_D[a:univ,b:univ,c:univ]{(pred_A[a] and pred_B[b]) or pred_C[c]}
   * </pre>
   * 
   * @return null
   * 
   * 
   */
  // TODO Other cases: RefExprs, LambdaExpr, just visit(result).
  @Override
public AlloyExpr visitAxPara(AxPara para) {
    if (para.getName().size() > 0) {
      System.err.println("Generic definitions not handled yet.");
      throw new RuntimeException();
    }
    ZSchText schText = para.getZSchText();
    if (schText.getZDeclList().size() == 1 &&
        schText.getZDeclList().get(0) instanceof ConstDecl) {
      visit(schText.getZDeclList().get(0));
    }
    else if (schText.getZDeclList().size() == 1) {
      AlloyExpr expr = visit(schText.getZDeclList().get(0));
      if (expr instanceof ExprVar) {
        ExprVar exprVar = (ExprVar) expr;
        if (exprVar.expr() instanceof Sig) {
          Sig sig = (Sig) exprVar.expr();
          SubsetSig subsetSig = new SubsetSig(exprVar.label(), sig);
          addSig(subsetSig);
          body = true;
          AlloyExpr pred = visit(schText.getPred());
          if (pred != null) {
            addSigPred(subsetSig, pred);
          }
          body = false;
        }
      }
    }
    return null;
  }

  @Override
public AlloyExpr visitConstDecl(ConstDecl cDecl) {
    try {
      String sigName = print(cDecl.getName());
      Expr result = cDecl.getExpr();
      if (unfolding_) {
        Source exprSource = new StringSource("normalize~"
            + print(cDecl.getName()));
        exprSource.setMarkup(Markup.LATEX);
        Expr toBeNormalized = ParseUtils
        .parseExpr(exprSource, section_, manager_);
        result = (Expr) preprocess(toBeNormalized);
        TypeCheckUtils.typecheck(result, manager_, false, false,
            section_);
      }
      // if (result instanceof ApplExpr) {
      //   System.err.println("Failed to normalize");
      //   throw new RuntimeException();
      // }
      names.put(result, sigName);
      if (result instanceof SchExpr2) {
        processSchExpr2((SchExpr2) result);
        return null;
      }
      if (result instanceof LambdaExpr) {
        visitLambdaAsFunc((LambdaExpr) result);
        return null;
      }
      if (result instanceof SchExpr) {
        return new SchExprVisitorImpl(sigName, null).visitSchExpr((SchExpr) result);
      }
      if (result instanceof ExistsExpr) {
        return new ExistsExprVisitorImpl(sigName).visitExistsExpr((ExistsExpr) result);
      }
      AlloyExpr value = visit(result);
      macros_.put(sigName, value);
      return null;
    } catch (CommandException e) {
      throw new RuntimeException(e);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }
  
  @Override
public AlloyExpr visitExpr(Expr expr) {
    return new ExprVisitorImpl(null).visitExpr(expr);
  }

  /**
   * creates a new enum
   * eg
   * 
   * <pre>
   * A ::= B | C | D
   * </pre>
   * 
   * translates to:
   * 
   * <pre>
   * enum A {B, C, C}
   * </pre>
   * 
   * @return null
   * 
   */
  @Override
public AlloyExpr visitFreePara(FreePara para) {
    return new FreetypeVisitorImpl().visitFreePara(para);
  }

  /**
   * translates into a sig for each name, with the given name <br>
   * eg
   * 
   * <pre>
   * [A, B, C]
   * </pre>
   * 
   * translates to:
   * 
   * <pre>
   * sig A {}
   * sig B {}
   * sig C {}
   * </pre>
   */
  @Override
public AlloyExpr visitGivenPara(GivenPara para) {
    for (Name name : para.getNames()) {
      module_.addSig(new PrimSig(print(name)));
    }
    return null;
  }

  /**
   * if a sig with the name of the givenType has been encountered before,
   * returns the sig. <br>
   * otherwise:
   * 
   * <pre>
   *           arithmos         =&gt; Int
   *           seq              =&gt; seq
   * </pre>
   * 
   * @return the sig, or null if no sig matches
   */
  @Override
public AlloyExpr visitGivenType(GivenType givenType) {
    if (print(givenType.getName()).equals(ZString.ARITHMOS)) {
      return SIGINT;
    }
    if (print(givenType.getName()).equals("seq")) {
      return SEQIDX;
    }
    return module_.getSig(print(givenType.getName()));
  }

  @Override
public AlloyExpr visitInclDecl(InclDecl inclDecl) {
    return visit(inclDecl.getExpr());
  }

  /** Ignore Latex markup paragraphs. */
  @Override
public AlloyExpr visitLatexMarkupPara(LatexMarkupPara para) {
    return null;
  }

  public Func visitLambdaAsFunc(LambdaExpr lambda) {
    String name = names.get(lambda);
    if (module_.containsFunc(name))
      return null;
    List<AlloyExpr> vars = new ZDeclListVisitorImpl().visitZDeclList(lambda.getZSchText().getZDeclList());
    this.body = true;
    AlloyExpr body = visit(lambda.getExpr());
    this.body = false;
    TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
    AlloyExpr returnDecl = visit(type);
    List<ExprVar> vars2 = new ArrayList<ExprVar>();
    for (AlloyExpr alloyExpr : vars) {
      if (alloyExpr instanceof ExprVar) {
        vars2.add((ExprVar) alloyExpr);
      }
    }
    
    Func func = new Func(name, vars2, returnDecl);
    if (body != null) func.setBody(body);
    module_.addFunc(func);
    return null;
  }

  /** Ignore narrative paragraphs. */
  @Override
public AlloyExpr visitNarrPara(NarrPara para) {
    return null;
  }

  /** Ignore operator templates. */
  @Override
public AlloyExpr visitOptempPara(OptempPara optempPara) {
    return null;
  }

  /**
   * if the type of the subexpression is not null, creates the set of the
   * translation
   * 
   * @return the expression, or null if the subexpression translates to null
   */
  @Override
public AlloyExpr visitPowerType(PowerType powerType) {
    AlloyExpr body = visit(powerType.getType());
    if (body == null) {
      System.err.println("body of power type must not be null: " + powerType);
      System.err.println("BODY: " + powerType.getType().getClass());
      throw new RuntimeException();
    }
    return body.setOf();
  }
  
  @Override
public AlloyExpr visitPred(Pred pred) {
    return new PredVisitorImpl().visitPred(pred);
  }

  /**
   * translates from a prodType to the equivalant expression in alloy
   * 
   * @return the expression or null if some of the sub expressions translate
   *         to null
   */
  @Override
public AlloyExpr visitProdType(ProdType prodType) {
    //		Expr prod = null;
    AlloyExpr first = null;
    AlloyExpr second = null;
    for (Type2 type : prodType.getType()) {
      AlloyExpr cont = visit(type);
      if (cont == null) {
        System.err.println("elements of ProdType must not be null");
        throw new RuntimeException();
      } else if (cont instanceof ExprUnary
          && ((ExprUnary) cont).op() == ExprUnary.Op.SETOF) {
        cont = ((ExprUnary) cont).sub();
      }
      if (first == null) {
        first = cont;
      } else {
        second = cont;
        return relationMap_.retrieve(first, second);
      }
    }
    System.err.println("this didn't work properly!");
    throw new RuntimeException();
  }

  /** Ignore rules. */
  @Override
public AlloyExpr visitRule(Rule r) {
    return null;
  }

  @Override
public AlloyExpr visitSchemaType(SchemaType schemaType) {
    // this doesn't really work. It matches the 'first' sig which has the
    // same number of fields, with the same names
    // could check the types
    // If there are two schemas with the same number and names of fields it
    // fails.
    Map<String, AlloyExpr> fields = new HashMap<String, AlloyExpr>();
    for (NameTypePair p : schemaType.getSignature().getNameTypePair()) {
      fields.put(print(p.getName()), visit(p.getType()));
    }

    for (Sig sig : module_.sigs()) {
      boolean equal = sig.fields().size() == fields.size();
      for (Field field : sig.fields()) {
        if (!fields.containsKey(field.label())) {
          equal = false;
        }
      }
      if (equal) {
        return sig;
      }
    }
    return null;
  }

  @Override
public AlloyExpr visitTypeAnn(TypeAnn typeAnn) {
    return visit(typeAnn.getType());
  }

  /**
   * creates a exprvar with the name and expr of the vDecl
   */
  @Override
public AlloyExpr visitVarDecl(VarDecl vDecl) {
    return new ExprVar(print(vDecl.getName()), visit(vDecl.getExpr()));
  }

  @Override
public AlloyExpr visitZSect(ZSect zSect) {
    String sect = "\\begin{zsection} "
      + "\\SECTION " + section_ + " " + "\\parents "
      + zSect.getName() + ", " + "expansion\\_rules, "
      + "simplification\\_rules" + "\\end{zsection}";
    Source specSource = new StringSource(sect, section_);
    specSource.setMarkup(Markup.LATEX);
    manager_.put(new Key<Source>(section_, Source.class), specSource);
    for (Para para : zSect.getZParaList()) {
      visit(para);
    }
    return null;
  }

  public static boolean isPostfixOperator(ZName name, String op) {
    try {
      OperatorName opName = new OperatorName(name);
      String[] opWords = opName.getWords();
      return opWords.length > 0 && op.equals(opWords[0]);
    } catch (OperatorName.OperatorNameException e) {
      return false;
    }
  }

  public static String isInfixOperator(ZName name) {
    try {
      OperatorName opName = new OperatorName(name);
      if (!opName.isInfix())
        return null;
      return opName.getWords()[1];
    } catch (OperatorName.OperatorNameException e) {
      return null;
    }
  }

  public static String isPrefixOperator(ZName name) {
    try {
      OperatorName opName = new OperatorName(name);
      if (!opName.isPrefix())
        return null;
      return opName.getWords()[1];
    } catch (OperatorName.OperatorNameException e) {
      return null;
    }
  }

  public static boolean isInfixOperator(ZName name, String op) {
    try {
      OperatorName opName = new OperatorName(name);
      String[] opWords = opName.getWords();
      return opWords.length > 0 && op.equals(opWords[1]);
    } catch (OperatorName.OperatorNameException e) {
      return false;
    }
  }

  public String print(Term t) {
    if (t != null)
      return t.accept(printVisitor_);
    else
      return "";
  }

  public AlloyExpr visit(Term t) {
    if (t != null) {
      return t.accept(this);
    }
    return null;
  }

  private Term preprocess(Term term) {
    try {
      RuleTable rules = manager_.get(new Key<RuleTable>(section_,
          RuleTable.class));
      RewriteVisitor rewriter = new RewriteVisitor(rules, manager_,
          section_);
      return Strategies.innermost(term, rewriter);
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  private AlloyExpr processSchExpr2(SchExpr2 schExpr2) {
    String schName = names.get(schExpr2);
    if (schName == null) {
      System.err.println("SchExpr2s must have names");
      throw new RuntimeException();
    }
    Sig sig = new PrimSig(schName);
    List<Field> exprs = fields(schExpr2);
    for (Field expr : exprs) {
      addField(sig, expr);
    }
    addSig(sig);
    addSigPred(sig, visit(schExpr2));
    return null;
  }
  //TODO clare document this beast
  public List<Field> fields(SchExpr2 schExpr2) {
    Map<String, AlloyExpr> fields = new HashMap<String, AlloyExpr>();
    Queue<SchExpr2> subexprs = new LinkedList<SchExpr2>();
    subexprs.offer(schExpr2);
    List<String> order = new ArrayList<String>();
    while (!subexprs.isEmpty()) {
      SchExpr2 subexpr = subexprs.poll();
      if (subexpr.getLeftExpr() instanceof RefExpr) {
        if (!fields.containsKey(print(subexpr.getLeftExpr()))) {
          AlloyExpr field = visit(subexpr.getLeftExpr());
          fields.put(print(subexpr.getLeftExpr()), field);
          order.add(print(subexpr.getLeftExpr()));
        }
      } else if (subexpr.getLeftExpr() instanceof SchExpr2) {
        subexprs.offer((SchExpr2) subexpr.getLeftExpr());
      }
      if (subexpr.getRightExpr() instanceof RefExpr) {
        if (!fields.containsKey(print(subexpr.getRightExpr()))) {
          AlloyExpr field = visit(subexpr.getRightExpr());
          fields.put(print(subexpr.getRightExpr()), field);
          order.add(print(subexpr.getRightExpr()));
        }
      } else if (subexpr.getRightExpr() instanceof SchExpr2) {
        subexprs.offer((SchExpr2) subexpr.getRightExpr());
      }
    }
    List<Field> fieldsList = new ArrayList<Field>();
    for(String l : order) {
      if (!(fields.get(l) instanceof Sig)) {
        System.err.println("error");
        throw new RuntimeException();
      }
      Sig s = (Sig) fields.get(l);
      fieldsList.addAll(s.fields());
    }
    return fieldsList;
  }

  /**
   * adds the signature to the module the most important thing this
   * does is set up the predicate - it creates a new pred which takes
   * all the fields of the signature as arguments, and sets the
   * predicate body to true a call to this pred is then set as the
   * constraint for the signature
   * 
   * this should therefore only be called after all the fields have
   * been included, otherwise the pred will have incorrect arguments
   * @param sig
   */
  public void addSig(Sig sig) {		
    module_.addSig(sig);
    List<ExprVar> vars = new ArrayList<ExprVar>();
    for (Field f : sig.fields()) {
      vars.add(new ExprVar(f.label(), f.expr()));
    }
    Func f = new Func("pred_" + sig.label(), vars);
    f.setBody(ExprConstant.TRUE);
    module_.addFunc(f);
    AlloyExpr[] fields = new AlloyExpr[sig.fields().size()];
    for (int i = 0; i < sig.fields().size(); i++)
      fields[i] = sig.fields().get(i);
    sig.addPred(f.call(fields));
  }

  /**
   * utility - adds a new constraint to a pred if the pred was true,
   * it replaces it, otherwise it is joined to the existing constraint
   * with 'and'
   */
  public void addSigPred(Sig sig, AlloyExpr pred) {
    Func existingPred = module_.getFunc("pred_" + sig);
    if (existingPred == null) {
      System.err.println("No pred for " + sig + " so " + pred
          + " cannot be added");
      throw new RuntimeException();
    }
    // (True and P) = P, so get rid of True's here
    // it might be nice if this happened in the ast?
    if (existingPred.getBody() == ExprConstant.TRUE) {
      existingPred.setBody(pred);
    } else {
      existingPred.setBody(existingPred.getBody().and(pred));
    }
  }

  private void addField(Sig sig, Field field) {
    if (! sig.containsField(field.label())) {
      sig.addField(field);
    }
  }

  @SuppressWarnings("unused")
  private void debug(Term t) throws PrintException {
    StringWriter foo = new StringWriter();
    PrintUtils.print(t, foo, manager_, section_, Markup.UNICODE);
    System.out.println("Debug: " + foo);
  }

  class AlloyPrintVisitor extends PrintVisitor implements
  DecorExprVisitor<String>, RefExprVisitor<String>, StrokeVisitor<String> {
    @Override
	public String visitZName(ZName zName) {
      String word = zName.getWord();
      word = word.replaceAll(ZString.DELTA, "Delta");
      word = word.replaceAll(ZString.XI, "Xi");
      word = word.replaceAll("\u03A6", "Phi");
      word = word.replaceAll("\u2295", "Distro");
      word = word.replaceAll("/", "Slash");
      if (names_.containsKey(zName.getId())) {
        return names_.get(zName.getId());
      }
      return word + visit(zName.getStrokeList());
    }

    @Override
	public String visitInStroke(InStroke inStroke) {
      return "_in";
    }

    @Override
	public String visitNextStroke(NextStroke nextStroke) {
      return "'";
    }

    @Override
	public String visitOutStroke(OutStroke outStroke) {
      return "_out";
    }

    @Override
	public String visitNumStroke(NumStroke numStroke) {
      return numStroke.getDigit().toString();
    }

    @Override
	public String visitDecorExpr(DecorExpr decorExpr) {
      return decorExpr.getExpr().accept(this)
      + decorExpr.getStroke().accept(this);
    }

    @Override
	public String visitRefExpr(RefExpr refExpr) {
      return refExpr.getName().accept(this);
    }

    @Override
    public String visitStroke(Stroke stroke) {
      return stroke.accept(this);
    }
  }
}
