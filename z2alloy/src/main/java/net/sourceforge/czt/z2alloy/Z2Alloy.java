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

import static net.sourceforge.czt.z2alloy.ast.Sig.NONE;
import static net.sourceforge.czt.z2alloy.ast.Sig.SEQIDX;
import static net.sourceforge.czt.z2alloy.ast.Sig.SIGINT;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;
import java.util.Map.Entry;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z2alloy.ast.*;
import net.sourceforge.czt.z2alloy.visitors.*;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.visitor.RuleVisitor;

public class Z2Alloy implements TermVisitor<AlloyExpr>,
AndExprVisitor<AlloyExpr>,
ApplExprVisitor<AlloyExpr>,
AxParaVisitor<AlloyExpr>,
BindSelExprVisitor<AlloyExpr>,
CompExprVisitor<AlloyExpr>,
ConstDeclVisitor<AlloyExpr>,
DecorExprVisitor<AlloyExpr>,
ExistsExprVisitor<AlloyExpr>,
Exists1PredVisitor<AlloyExpr>,
ExistsPredVisitor<AlloyExpr>,
ForallPredVisitor<AlloyExpr>,
FreeParaVisitor<AlloyExpr>,
GivenParaVisitor<AlloyExpr>,
GivenTypeVisitor<AlloyExpr>,
HideExprVisitor<AlloyExpr>,
IffExprVisitor<AlloyExpr>,
ImpliesExprVisitor<AlloyExpr>,
InclDeclVisitor<AlloyExpr>,
LambdaExprVisitor<AlloyExpr>,
LatexMarkupParaVisitor<AlloyExpr>,
MemPredVisitor<AlloyExpr>,
NarrParaVisitor<AlloyExpr>,
NegPredVisitor<AlloyExpr>,
NumExprVisitor<AlloyExpr>,
OptempParaVisitor<AlloyExpr>,
OrExprVisitor<AlloyExpr>,
PowerExprVisitor<AlloyExpr>,
PowerTypeVisitor<AlloyExpr>,
Pred2Visitor<AlloyExpr>,
ProdExprVisitor<AlloyExpr>,
ProdTypeVisitor<AlloyExpr>,
RefExprVisitor<AlloyExpr>,
RuleVisitor<AlloyExpr>,
SchemaTypeVisitor<AlloyExpr>,
SchExprVisitor<AlloyExpr>,
SetCompExprVisitor<AlloyExpr>,
SetExprVisitor<AlloyExpr>,
ThetaExprVisitor<AlloyExpr>,
TruePredVisitor<AlloyExpr>,
TupleExprVisitor<AlloyExpr>,
TypeAnnVisitor<AlloyExpr>,
VarDeclVisitor<AlloyExpr>,
ZDeclListVisitor<AlloyExpr>,
ZExprListVisitor<AlloyExpr>,
ZSectVisitor<AlloyExpr>
{
  private SectionManager manager_;
  private AlloyPrintVisitor printVisitor_ = new AlloyPrintVisitor();
  private String section_ = "z2alloy";
  private boolean unfolding_ = false;
  private List<ExprVar> vars_;
  private List<AlloyExpr> exprs_;

  private boolean body = false;

  private Module module_ = new Module();
  private RelationMap relationMap_ = new RelationMap(module_);

  private Map<String, AlloyExpr> macros_ = new HashMap<String, AlloyExpr>();

  private Map<String, AlloyExpr> fields_ = new HashMap<String, AlloyExpr>();

  private Stack<Term> stack = new Stack<Term>();

  private List<ExprVar> thetaQuantified = new ArrayList<ExprVar>();
  private AlloyExpr thetaPred = ExprConstant.TRUE;

  /**
   * A mapping from ZName ids to alloy names.
   */

  private Map<Expr, String> names =
    new HashMap<Expr, String>();

  private Map<String, String> names_ = new HashMap<String, String>();

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

  // ==================== Visitor Methods ==================

  public AlloyExpr visitTerm(Term term) {
    System.err.println(term.getClass() + " not yet implemented");
    throw new RuntimeException(print(term));
  }

  /**
   * translates an and expression (schema conjunction) into an alloy and
   * expression. The schemas are translated into a call to the predicate
   * translated by the schema
   * 
   * eg
   * 
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \land B =&gt; pred_A[a] and pred_B[b]
   * </pre>
   * 
   * Currently the actual variables from the signiture are not used in the
   * pred calls. Instead new ones are created. This works, assuming the
   * variables are declared with the same name as in the predicate
   * declaration.
   * 
   * @return the expression
   */
  public AlloyExpr visitAndExpr(AndExpr andExpr) {
    Pair<AlloyExpr, AlloyExpr> comps = schExpr2SigComponent(andExpr);
    return comps.getFirst().and(comps.getSecond());
  }

  /**
   * translates a function application <br>
   * types of application expressions currently translated:
   * 
   * <pre>
   * union                      left + right
   * relational override        left ++ right
   * rightwards arrow from bar  left -&gt; right
   * ndres                      calls ndres[left, right]
   * implication                left =&gt; right
   * ..                         {i : Int | i &gt;= left and i &lt;= right}
   * dom                        calls dom[right]
   * ran						  calls ran[right]
   * addition					  left + right
   * substraction				  left - right
   * dres						  left <: right
   * </pre>
   * 
   * otherwise tries left.right
   * 
   * @return the expression if it successfully translated, or null it
   *         something fails
   */
  public AlloyExpr visitApplExpr(ApplExpr applExpr) {
    AlloyExpr ret = null;
    if (applExpr.getMixfix()) {
      if (applExpr.getRightExpr() instanceof TupleExpr
          && applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        String binOp = isInfixOperator(refExpr.getZName());
        ZExprList exprs = ((TupleExpr) applExpr.getRightExpr()).getZExprList();
        AlloyExpr left = visit(exprs.get(0));
        AlloyExpr right = visit(exprs.get(1));
        if (left == null || right == null) {
          System.err.println("left and right of a binary expression must not be null");
          throw new RuntimeException();
        }
        if (binOp == null) {
          // this means it isn't an infix operator?
        }
        else if (binOp.equals(ZString.CUP)) {
          ret = left.plus(right);
        }
        else if (binOp.equals(ZString.OPLUS)) {
          ret = left.override(right);
        }
        else if (binOp.equals(ZString.MAPSTO)) {
          ret = left.product(right);
        }
        else if (binOp.equals(ZString.NDRES)) {
          List<AlloyExpr> args = new ArrayList<AlloyExpr>();
          args.add(left);
          args.add(right);
          if (module_.containsFunc("ndres"))
            ret = module_.getFunc("ndres").call(args);
        }
        else if (binOp.equals(ZString.DRES)) {
          ret = left.domain(right);
        }
        else if (binOp.equals(ZString.IMP)) {
          ret = left.implies(right);
        }
        else if (binOp.equals("..")) {
          ExprVar i = new ExprVar("i", SIGINT);
          AlloyExpr pred = i.gte(left).and(i.lte(right));
          ret = pred.comprehensionOver(Arrays
              .asList(new ExprVar[] { i }));
        }
        else if (binOp.equals(ZString.CAT)) {
          if (module_.containsFunc("append"))
            ret = module_.getFunc("append").call(left, right);
        }
        else if (binOp.equals(ZString.MINUS)) {
          if (module_.containsFunc("sub")) {
            ret = module_.getFunc("sub").call(left, right);
          }
        }
        else if (binOp.equals(ZString.PLUS)) {
          if (module_.containsFunc("add")) {
            ret = module_.getFunc("add").call(left, right);
          }
        }
        else if (binOp.equals(ZString.MULT)) {
          if (module_.containsFunc("mul")) {
            ret = module_.getFunc("mul").call(left, right);
          }
        }
        else if (binOp.equals("div")) {
          if (module_.containsFunc("div")) {
            ret = module_.getFunc("div").call(left, right);
          }
        }
        else if (binOp.equals("mod")) {
          if (module_.containsFunc("rem")) {
            ret = module_.getFunc("rem").call(left, right);
          }
        }
        else {
          System.err.println("ApplExpr " + binOp + " not yet implemented");
          throw new RuntimeException();
        }
      }
      else if (applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        AlloyExpr body = visit(applExpr.getRightExpr());
        if (print(refExpr.getName()).equals(ZString.LANGLE + " ,, " + ZString.RANGLE)) { // sequence
          if (body == NONE) {
            ret = NONE.product(NONE);
          } else {
            System.err.println("non empty sequences not translated yet");
            throw new RuntimeException();
          }
        }
        else if (print(refExpr.getName()).equals("# _ ")) {
          ret = body.cardinality();
        }
        else if (print(refExpr.getName()).equals("- _ ")) {
          if (module_.containsFunc("negate"))
            ret = module_.getFunc("negate").call(body);
        }
        else if (print(refExpr.getName()).equals("succ _ ")) {
          if (module_.containsFunc("next"))
            ret = module_.getFunc("next").call(body);
        }
      }
    }
    else { // application
      if (applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        String name = print(refExpr.getName());
        if (name.equals("dom")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (module_.containsFunc("dom"))
            ret = module_.getFunc("dom").call(body);
        }
        else if (name.equals("ran")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (module_.containsFunc("ran")) 
            ret = module_.getFunc("ran").call(body);
        }
        else if (name.equals("last")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (module_.containsFunc("last"))
            ret = module_.getFunc("last").call(body);
        }
        else if (name.equals("front")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (module_.containsFunc("front"))
            ret = module_.getFunc("front").call(body);
        }
        else if (module_.containsFunc(print(refExpr.getZName()))) {
          Func fun = module_.getFunc(print(refExpr.getZName()));
          if (applExpr.getRightExpr() instanceof TupleExpr) {
            AlloyExpr first = visit(applExpr.getRightExpr());
            if (first != null) {
              exprs_.add(0, first);
            }
            ret = fun.call(exprs_);
          }
          AlloyExpr body = visit(applExpr.getRightExpr());
          ret = fun.call(body);
        }
      }
    }
    if (ret == null) {
      AlloyExpr left = visit(applExpr.getLeftExpr());
      AlloyExpr right = visit(applExpr.getRightExpr());

      if (left == null || right == null) {
        System.err.println("left and right exprs must not be null in an ApplExpr");
        throw new RuntimeException();
      }
      ret = right.join(left);
    }
    ret = processRelation(ret, applExpr);
    return ret;
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

  // TODO figure out wtf this is supposed to be
  public AlloyExpr visitBindSelExpr(BindSelExpr bindSelExpr) {
    AlloyExpr left = visit(bindSelExpr.getExpr());
    ExprVar right = new ExprVar(print(bindSelExpr.getName()));
    return left.join(right);
  }

  // TODO figure out wtf this is supposed to be
  public AlloyExpr visitCompExpr(CompExpr compExpr) {
    AlloyExpr leftExpr = visit(compExpr.getLeftExpr());
    AlloyExpr rightExpr = visit(compExpr.getRightExpr());
    if (leftExpr instanceof Sig && rightExpr instanceof Sig) {
      Sig left = (Sig) leftExpr;
      Sig right = (Sig) rightExpr;
      // assumes it comes from the first element
      AlloyExpr leftmost = left.pred();
      if (! (leftmost instanceof ExprCall)) {
        return null;
      }
      leftmost = ((ExprCall) leftmost).fun().body();
      while (!(leftmost instanceof ExprCall)) {
        if (leftmost instanceof ExprUnary) {
          leftmost = ((ExprUnary) leftmost).sub();
        }
        else if (leftmost instanceof ExprBinary) {
          leftmost = ((ExprBinary) leftmost).left();
        }
        else {
          System.err.println("not translated " + leftmost.getClass());
          throw new RuntimeException();
        }
      }
      String name = ((ExprCall) leftmost).fun().label().substring(10);
      if (! module_.containsSig(name)) {
        System.err.println("not translated");
        throw new RuntimeException();
      }
      Sig quant = module_.getSig(name);
      ExprVar quantSig = new ExprVar("temp", quant);
      List<ExprVar> vars = new ArrayList<ExprVar>();
      vars.add(quantSig);
      List<AlloyExpr> vars1 = new ArrayList<AlloyExpr>();
      List<AlloyExpr> vars2 = new ArrayList<AlloyExpr>();
      for (Field f : quant) {
        vars1.add(new ExprVar(f.label(), f.expr()));
        vars1.add(quantSig.join(f));
        vars2.add(quantSig.join(f));
        vars2.add(new ExprVar(f.label() + "'", f.expr()));
      }
      Func predleft = module_.getFunc("pred_" + left.label());
      Func predRight = module_.getFunc("pred_" + right.label());
      return predleft.call(vars1).and(predRight.call(vars2)).forSome(vars);
    }
    else {
      System.err.println("not implemented");
      throw new RuntimeException();
    }
  }

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
        TypeCheckUtils.typecheck(result, manager_, false,
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
        return new SchExprVisitorImpl(sigName).visitSchExpr((SchExpr) result);
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

  public AlloyExpr visitDecorExpr(DecorExpr decorExpr) {
    AlloyExpr expr = visit(decorExpr.getExpr());
    if (expr instanceof Sig) {
      Sig sig = (Sig) expr;
      Sig sigStroke = new PrimSig(sig.label() + print(decorExpr.getStroke()));
      for (Field field : sig) {
        sigStroke.addField(new Field(field.label()
            + print(decorExpr.getStroke()),
            field.expr()));
      }
      return sigStroke;
    }
    else {
      System.err.println("not yet translated");
      throw new RuntimeException();
    }
  }

  /**
   * Creates a new signiture which contains all the fields in the predicate
   * schemas, except those in schemas quantified over <br>
   * Includes a signiture predicate which is an exists predicate translated
   * from the schema predicate, with the additon that any fields in more than
   * one predicate schema are equal <br>
   * eg
   * 
   * <pre>
   * A == \exists B, C @ D \and E
   * </pre>
   * 
   * <br>
   * where B has fields b:X, C has fields b:X, c:Y, D has fields b : X, c : Y,
   * d : Z, E has field b : X translates to:
   * 
   * <pre>
   * sig A {
   *    d : Z
   * }{pred_A[d]}
   * pred pred_A[d : Z] {
   *    some b_temp : B, c_temp : C | pred_D[c_temp.b, c_temp.c, d] and pred_E[c_temp.b] and c_temp.b = b_temp.b
   * }
   * 
   */
  public AlloyExpr visitExistsExpr(ExistsExpr existsExpr) {
    /*
     * basically this method accumulates all the fields of predicate bits,
     * then removes all fields in exists sigs the ones left over are the
     * fields for the new signiture
     * 
     * then it creates all the predicate - using build which makes the
     * predicate calls to the sigs from either the arguments of the
     * predicate (fields of the new sig) or joins between the fields of the
     * exists sigs and the sigs
     * 
     * also needs to find exists sigs with matching fields and ensure they
     * are equal
     */
    ZDeclList incl = existsExpr.getZSchText().getZDeclList();
    List<Sig> inclSigs = new ArrayList<Sig>(); // the sigs quantified over
    ExprVar[] inclVars = new ExprVar[incl.size() - 1]; // the variables of
    // the sigs
    // quantified over
    // treats the first one separatly just for the call at the end
    Sig s = (Sig) visit(((InclDecl) incl.get(0)).getExpr());
    inclSigs.add(s);
    ExprVar first = (new ExprVar(s.label().toLowerCase() + "_temp", s));
    for (int i = 1; i < incl.size(); i++) {
      s = (Sig) visit(((InclDecl) incl.get(i)).getExpr());
      inclSigs.add(s);
      inclVars[i - 1] = (new ExprVar(s.label().toLowerCase() + "_temp", s));
    }
    body = true;
    AlloyExpr pred = visit(existsExpr.getExpr());
    body = false;
    List<Sig> predSigs = new ArrayList<Sig>(); // all the sigs in the body
    // of the predicate
    Stack<AlloyExpr> predParts = new Stack<AlloyExpr>(); // just for accumulating them
    // above
    predParts.add(pred);
    while (!predParts.isEmpty()) {
      AlloyExpr temp = predParts.pop();
      if (temp instanceof Sig) {
        predSigs.add((Sig) temp);
      } else if (temp instanceof ExprCall) {
        predSigs.add(module_.getSig(((ExprCall) temp).fun().label()
            .replaceFirst("pred_", "")));
      } else {
        System.err.println("Not fully translated: " + temp.getClass()
            + " " + temp);
        throw new RuntimeException();
      }
    }
    Map<String, AlloyExpr> fields = new HashMap<String, AlloyExpr>(); // the fields
    // for the new signiture
    Map<String, AlloyExpr> vars = new HashMap<String, AlloyExpr>(); // the expressions
    // to be used in predicate calls
    for (Sig sig : predSigs) {
      for (Field field : sig.fields()) {
        fields.put(field.label(), field.expr());
        vars.put(field.label(),
            new ExprVar(field.label(), field.expr()));
      }
    }
    for (int i = 0; i < inclSigs.size(); i++) {
      for (Field field : inclSigs.get(i).fields()) {
        fields.remove(field.label()); // fields in the quantified over
        // sigs should not be in the signiture
        if (i == 0) {
          vars.put(field.label(), first.join(field.expr()));
          // remember vars does not include them first because of the call at the end
        } else {
          vars.put(field.label(), inclVars[i - 1].join(field.expr()));
        }
      }
    }
    PrimSig sig;
    sig = new PrimSig(names.get(existsExpr));
    for (Entry<String, AlloyExpr> field : fields.entrySet()) {
      sig.addField(new Field(field.getKey(), field.getValue()));
    }
    addSig(sig);
    // unfolds the pred and builds it up into a tree contianing the pred
    // calls, ands, ors
    AlloyExpr predBody = build(pred, vars);
    // the name of the duplicate field, and the list of expressions
    // the expressions are such that they can be directly used in the
    // equality expression
    Map<String, List<AlloyExpr>> dupFields = new HashMap<String, List<AlloyExpr>>();
    for (int i = 0; i < inclSigs.size(); i++) {
      for (Field field : inclSigs.get(i).fields()) {
        if (!dupFields.containsKey(field.label())) {
          dupFields.put(field.label(), new ArrayList<AlloyExpr>());
        }
        if (i == 0) { // remember vars does not include the first
          // because of the call at the end
          dupFields.get(field.label()).add(first.join(field.expr()));
        }
        else {
          dupFields.get(field.label()).add(inclVars[i - 1].join(field.expr()));
        }
      }
    }
    // starts from the second entry, and puts all the later entries equal to
    // the first
    // ie looks like first=second and first=third and first=fourth ...
    for (Entry<String, List<AlloyExpr>> entry : dupFields.entrySet()) {
      for (int i = 1; i < entry.getValue().size(); i++) {
        AlloyExpr firstExpr = entry.getValue().get(0);
        AlloyExpr ithExpr = entry.getValue().get(i);
        if (predBody == null) {
          predBody = firstExpr.equal(ithExpr);
        }
        else {
          predBody = predBody.and(firstExpr.equal(ithExpr));
        }
      }
    }
    vars_.add(first);
    addSigPred(sig, predBody.forSome(vars_));
    return null;
  }

  /**
   * uses visit to recursively translate variables and predicates.
   * 
   * <pre>
   * \exists_1 var1, ... varn @ pred1 | pred2
   * </pre>
   * 
   * translates to :
   * 
   * <pre>
   * one var1, ..., varn | pred1 and pred2
   * </pre>
   * 
   * @return the expression, or null if something is null that should not be
   */
  public AlloyExpr visitExists1Pred(Exists1Pred exists1Pred) {
    ExprVar firstVar = (ExprVar) visit(exists1Pred.getZSchText()
        .getZDeclList());
    List<ExprVar> rest = vars_;
    AlloyExpr pred;
    body = true;
    AlloyExpr pred1 = visit(exists1Pred.getZSchText().getPred());
    AlloyExpr pred2 = visit(exists1Pred.getPred());
    body = false;
    if (pred2 == null) {
      System.err.println("pred of ExistsPred must not be null");
      throw new RuntimeException();
    }
    if (pred1 == null) {
      pred = pred2;
    }
    else {
      pred = pred1.and(pred2);
    }
    rest.add(firstVar);
    return pred.forOne(rest);
  }

  /**
   * uses visit to recursively translate variables and predicates.
   * 
   * <pre>
   * \exists var1, ..., varn @ pred1 | pred2
   * </pre>
   * 
   * translates to
   * 
   * <pre>
   * some var1, ... var2 | pred1 and pred2
   * </pre>
   * 
   * @return the epxression, or null if something is null that should not be
   */
  public AlloyExpr visitExistsPred(ExistsPred existsPred) {
    ExprVar firstVar = null;
    AlloyExpr first = visit(existsPred.getZSchText().getZDeclList());
    AlloyExpr sigPred = null;
    List<ExprVar> rest = vars_;		

    if (first instanceof ExprVar) firstVar = (ExprVar) first;
    else if (first instanceof Sig) {
      List<AlloyExpr> sigCallVars = new ArrayList<AlloyExpr>();
      Sig s = (Sig) first;
      for (Field f : s) {
        ExprVar temp = new ExprVar(f.label(), f.expr());
        sigCallVars.add(temp);
        if (s.fields().get(0).equals(f)) {
          firstVar = temp;
        }
        else {
          vars_.add(temp);
        }
      }
      sigPred = module_.getFunc("pred_" + s.label()).call(sigCallVars);
    }
    AlloyExpr pred;
    body = true;
    AlloyExpr pred1 = visit(existsPred.getZSchText().getPred());
    AlloyExpr pred2 = visit(existsPred.getPred());
    body = false;
    if (pred2 == null) {
      System.err.println("pred of ExistsPred must not be null");
      throw new RuntimeException();
    }
    if (sigPred != null) {
      if( pred1 == null) {
        pred1 = sigPred;
      }
      else {
        pred1 = pred1.and(sigPred);
      }
    }
    if (pred1 == null) {
      pred = pred2;
    } else {
      pred = pred1.and(pred2);
    }
    if (! thetaQuantified.isEmpty()) {
      pred = thetaPred.and(pred).forSome(thetaQuantified);
      thetaPred = ExprConstant.TRUE;
      thetaQuantified.clear();
    }
    if (firstVar == null) {
      System.err.println("firstVar of ExistsPred must not be null");
      throw new RuntimeException();
    }
    rest.add(firstVar);
    return pred.forSome(rest);
  }

  /**
   * uses visit to recurisvely translate variables and predicates
   * 
   * <pre>
   * \forall var1, ..., varn @ pred1 | pred2
   * </pre>
   * 
   * translates to:
   * 
   * <pre>
   * all var1, ..., var2 | pred1 =&gt; pred2
   * </pre>
   */
  public AlloyExpr visitForallPred(ForallPred allPred) {
    ExprVar firstVar = (ExprVar) visit(allPred.getZSchText().getZDeclList());
    List<ExprVar> rest = vars_;
    AlloyExpr pred;
    body = true;
    AlloyExpr pred1 = visit(allPred.getZSchText().getPred());
    AlloyExpr pred2 = visit(allPred.getPred());
    body = false;
    if (pred2 == null) {
      System.err.println("pred of allpred must not be null");
      throw new RuntimeException();
    }
    if (pred1 == null) {
      pred = pred2;
    } else {
      pred = pred1.implies(pred2);
    }
    if (firstVar == null) {
      System.err.println("fistVar of allpred must not be null");
      throw new RuntimeException();
    }
    rest.add(firstVar);
    return pred.forAll(rest);
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
  public AlloyExpr visitHideExpr(HideExpr hideExpr) {
    Sig newSig = new PrimSig(names.get(hideExpr));
    List<String> hiddenNames = new ArrayList<String>();
    for (Name n : hideExpr.getZNameList()) hiddenNames.add(print(n));
    List<ExprVar> hidden = new ArrayList<ExprVar>();
    List<String> hiddenNamesIncluded = new ArrayList<String>();
    List<Field> fields = new ArrayList<Field>();
    AlloyExpr sub = null;
    if (hideExpr.getExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) hideExpr.getExpr();
      AlloyExpr expr = visit(refExpr);
      if (expr instanceof Sig) {
        Sig sig = (Sig) expr;
        fields = sig.fields();
        sub = sig.pred();
      }
      else {
        System.err.println("class: " + hideExpr.getExpr().getClass());
        System.err.println(hideExpr.getClass() + " not currently translated");
        throw new RuntimeException();
      }
    }
    else if (hideExpr.getExpr() instanceof SchExpr2) {
      SchExpr2 schExpr2 = (SchExpr2) hideExpr.getExpr();
      fields = fields(schExpr2);
      sub = visit(schExpr2);
    }
    else {
      System.err.println("class: " + hideExpr.getExpr().getClass());
      System.err.println(hideExpr.getClass() + " not currently translated");
      throw new RuntimeException();
    }
    for (Field f : fields) {
      if (hiddenNames.contains(f.label()) &&
          ! hiddenNamesIncluded.contains(f.label())) {
        hidden.add(new ExprVar(f.label(), f.expr()));
        hiddenNamesIncluded.add(f.label());
      }
      else if (! hiddenNames.contains(f.label()))
        newSig.addField(f);
    }
    addSig(newSig);
    addSigPred(newSig, new ExprQuant(ExprQuant.Op.SOME, hidden, sub));
    return newSig;
  }

  /**
   * translates an iff expression (schema equivalance) into an alloy iff
   * expression. The schemas are translated into a call to the predicate
   * translated by the schema
   * 
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \iff B =&gt; pred_A[a] &lt;=&gt; pred_B[b]
   * </pre>
   * 
   * Currently the actual variables from the signiture are not used in the
   * pred calls. Instead new ones are created. This works, assuming the
   * variables are declared with the same name as in the predicate
   * declaration.
   * 
   * @return the expression
   */
  public AlloyExpr visitIffExpr(IffExpr iffExpr) {
    Pair<AlloyExpr, AlloyExpr> comps = schExpr2SigComponent(iffExpr);
    return comps.getFirst().iff(comps.getSecond());
  }

  /**
   * translates an implies expression (schema implication) into an alloy
   * implies expression. The schemas are translated into a call to the
   * predicate translated by the schema
   * 
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \implies B =&gt; pred_A[a] =&gt; pred_B[b]
   * </pre>
   * 
   * Currently the actual variables from the signiture are not used in the
   * pred calls. Instead new ones are created. This works, assuming the
   * variables are declared with the same name as in the predicate
   * declaration.
   * 
   * @return the expression
   */
  public AlloyExpr visitImpliesExpr(ImpliesExpr impliesExpr) {
    Pair<AlloyExpr, AlloyExpr> comps = schExpr2SigComponent(impliesExpr);
    return comps.getFirst().implies(comps.getSecond());
  }

  public AlloyExpr visitInclDecl(InclDecl inclDecl) {
    return visit(inclDecl.getExpr());
  }

  /** Ignore Latex markup paragraphs. */
  public AlloyExpr visitLatexMarkupPara(LatexMarkupPara para) {
    return null;
  }

  public AlloyExpr visitLambdaExpr(LambdaExpr lambda) {
    String name = names.get(lambda);
    if (module_.containsFunc(name)) return null;
    List<ExprVar> vars = new ArrayList<ExprVar>();
    vars.add((ExprVar) visit(lambda.getZSchText().getZDeclList()));
    if (vars_ != null) {
      for (ExprVar exprVar : vars_) {
        vars.add(exprVar);
      }
    }
    body = true;
    AlloyExpr body = visit(lambda.getExpr());
    this.body = false;
    TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
    AlloyExpr returnDecl = visit(type);
    ExprVar j = new ExprVar("j", returnDecl);
    vars.add(j);
    ExprQuant exprQuant =
      new ExprQuant(ExprQuant.Op.COMPREHENSION, vars, j.equal(body)); 
    return exprQuant;
  }

  public Func visitLambdaAsFunc(LambdaExpr lambda) {
    String name = names.get(lambda);
    if (module_.containsFunc(name))
      return null;
    List<ExprVar> vars = new ArrayList<ExprVar>();
    vars.add((ExprVar) visit(lambda.getZSchText().getZDeclList()));
    if (vars_ != null) {
      for (ExprVar exprVar : vars_) {
        vars.add(exprVar);
      }
    }
    this.body = true;
    AlloyExpr body = visit(lambda.getExpr());
    this.body = false;
    TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
    AlloyExpr returnDecl = visit(type);
    Func func = new Func(name, vars, returnDecl);
    if (body != null) func.setBody(body);
    module_.addFunc(func);
    return null;
  }

  /**
   * kinds of MemPred currently translated:
   * 
   * <pre>
   * equality                   left = right
   * notin                      ! left in right
   * subseteq                   left in right
   * subset                     left in right and (not left = right)
   * less                       left &lt; right
   * leq                        left &lt;= right
   * greater                    left &gt; right
   * geq                        left &gt;= right
   * neq                        ! left = right
   * </pre>
   * 
   * otherwise assumes it is membership => left in right
   */
  public AlloyExpr visitMemPred(MemPred memPred) {
    if (memPred.getRightExpr() instanceof SetExpr
        && ((SetExpr) memPred.getRightExpr()).getZExprList().size() == 1) {
      // equality
      AlloyExpr left = visit(memPred.getLeftExpr());
      AlloyExpr right = visit(memPred.getRightExpr());
      if (left == null || right == null) {
        System.err.println("Left and right of memPred must be non null");
        throw new RuntimeException();
      }
      return left.equal(right);
    }
    if (memPred.getLeftExpr() instanceof TupleExpr
        && memPred.getRightExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) memPred.getRightExpr();
      ZExprList exprs = ((TupleExpr) memPred.getLeftExpr()).getZExprList();
      AlloyExpr left = visit(exprs.get(0));
      AlloyExpr right = visit(exprs.get(1));
      if (left == null || right == null) {
        System.err.println("Left and right of refExpr must be non null");
        throw new RuntimeException();
      }
      if (isInfixOperator(refExpr.getZName(), ZString.NOTMEM)) {
        return left.in(right).not();
      }
      if (isInfixOperator(refExpr.getZName(), ZString.SUBSETEQ)) {
        return left.in(right);
      }
      if (isInfixOperator(refExpr.getZName(), ZString.SUBSET)) {
        return left.in(right).and(left.equal(right).not());
      }
      if (isInfixOperator(refExpr.getZName(), ZString.LESS)) {
        return left.lt(right);
      }
      if (isInfixOperator(refExpr.getZName(), ZString.LEQ)) {
        return left.lte(right);
      }
      if (isInfixOperator(refExpr.getZName(), ZString.GREATER)) {
        return left.gt(right);
      }
      if (isInfixOperator(refExpr.getZName(), ZString.GEQ)) {
        return left.gte(right);
      }
      if (isInfixOperator(refExpr.getZName(), ZString.NEQ)) {
        return left.equal(right).not();
      }
    }
    AlloyExpr left = visit(memPred.getLeftExpr());
    AlloyExpr right = visit(memPred.getRightExpr());
    if (left == null || right == null) {
      System.err.println("Left and right Expr of MemPred must not be null");
      throw new RuntimeException();
    }
    return left.in(right);
  }

  /** Ignore narrative paragraphs. */
  public AlloyExpr visitNarrPara(NarrPara para) {
    return null;
  }
  
  public AlloyExpr visitNegPred(NegPred negPred) {
    return visit(negPred.getPred()).not();
  }

  /** Ignore operator templates. */
  public AlloyExpr visitOptempPara(OptempPara optempPara) {
    return null;
  }

  /**
   * @return an alloy integer expression with the given value
   */
  public AlloyExpr visitNumExpr(NumExpr numexpr) {
    return ExprConstant.makeNUMBER(numexpr.getValue().intValue());
  }

  /**
   * translates an or expression (schema disjunction) into an alloy or
   * expression. The schemas are translated into a call to the predicate
   * translated by the schema <br>
   * eg
   * 
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \lor B =&gt; pred_A[a] or pred_B[b]
   * </pre>
   * 
   * Currently the actual variables from the signiture are not used in the
   * pred calls. Instead new ones are created. This works, assuming the
   * variables are declared with the same name as in the predicate
   * declaration.
   * 
   * @return the expression
   */
  public AlloyExpr visitOrExpr(OrExpr orExpr) {
    Pair<AlloyExpr, AlloyExpr> comps = schExpr2SigComponent(orExpr);
    return comps.getFirst().or(comps.getSecond());
  }

  public AlloyExpr visitPred2(Pred2 pred2) {
    return new Pred2VisitorImpl().visit(pred2);
  }

  /**
   * recursively calls visit on the sub expression and creates an alloy set of
   * the translation
   * 
   * @return the expression or null if the sub expression translates to null
   */
  public AlloyExpr visitPowerExpr(PowerExpr powerExpr) {
    AlloyExpr body = visit(powerExpr.getExpr());
    if (body == null) {
      System.err.println("body of power expr must not be null");
      throw new RuntimeException();
    }
    return body.setOf();
  }

  /**
   * if the type of the subexpression is not null, creates the set of the
   * translation
   * 
   * @return the expression, or null if the subexpression translates to null
   */
  public AlloyExpr visitPowerType(PowerType powerType) {
    AlloyExpr body = visit(powerType.getType());
    if (body == null) {
      System.err.println("body of power type must not be null: " + powerType);
      System.err.println("BODY: " + powerType.getType().getClass());
      throw new RuntimeException();
    }
    return body.setOf();
  }

  /**
   * translates from a z prod expr to an alloy version using visit to
   * recursively translate the sub expressions <br/>
   * eg
   * 
   * <pre>m,jk
   * expr1 \cross ... \cross exprn =&gt; expr1 -&gt; ... -&gt; exprn
   * </pre>
   * 
   * @return the expression or null if any of the sub expressions
   *         translate to null
   */
  public AlloyExpr visitProdExpr(ProdExpr prodExpr) {
    AlloyExpr expr = visit(prodExpr.getZExprList().get(0));
    for (int i = 1; i < prodExpr.getZExprList().size(); i++) {
      AlloyExpr current = visit(prodExpr.getZExprList().get(i));
      if (current == null || expr == null) {
        System.err.println("body of prodexprs must not be  null");
        throw new RuntimeException();
      }
      expr = expr.product(current);
    }
    return expr;
  }

  /**
   * translates from a prodType to the equivalant expression in alloy
   * 
   * @return the expression or null if some of the sub expressions translate
   *         to null
   */
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

  /**
   * kinds of RefExpr translated: <br>
   * subexprs are translated recursively using visit
   * 
   * <pre>
   * pfun               expr0 -&gt; lone expr1
   * rel				  expr0 -&gt; expr1
   * seq                seq expr0
   * arithmos           Int
   * nat                nat[]
   * </pre>
   * 
   * otherwise if the name has is that of an already encountered
   * signiture, it uses that signiture <br> finally it creates an
   * ExprVar with the given name and a type from the type annotations.
   */
  public AlloyExpr visitRefExpr(RefExpr refExpr) {
    String name = print(refExpr.getName());
    AlloyExpr ret = null;
    if (isInfixOperator(refExpr.getZName(), ZString.PFUN)) {
      ret = relationMap_.createPFun(visit(refExpr.getZExprList().get(0)),
          visit(refExpr.getZExprList().get(1)));
    }
    else if (isInfixOperator(refExpr.getZName(), ZString.REL)) {
      ret = relationMap_.create(visit(refExpr.getZExprList().get(0)),
          visit(refExpr.getZExprList().get(1)));
    }
    else if (isPostfixOperator(refExpr.getZName(), "seq")) {
      ret = relationMap_.createSeq(visit(refExpr.getZExprList().get(0)));
    }
    else if (print(refExpr.getZName()).equals(ZString.ARITHMOS)) {
      ret = SIGINT;
    }
    else if (print(refExpr.getZName()).equals(ZString.NAT)) {
      ExprVar i = new ExprVar("i", SIGINT);
      AlloyExpr sub = i.gte(ExprConstant.ZERO);
      List<ExprVar> vars = new ArrayList<ExprVar>();
      vars.add(i);
      ret = sub.comprehensionOver(vars);
    }
    else if (print(refExpr.getZName()).equals(ZString.NUM)) {
      ret = SIGINT;
    }
    else if (print(refExpr.getZName()).equals(ZString.EMPTYSET)) {
      AlloyExpr type = visit(refExpr.getAnn(TypeAnn.class));
      int num = arity(type);
      ret = NONE;
      for (int i = 1; i < num; i++) ret = NONE.product(NONE);
    }
    else if (module_.containsSig(name)) {
      ret = module_.getSig(name);
    }
    else if (name.contains("Delta")
        && module_.containsSig(name.replaceFirst("Delta", ""))) {
      ret = addDelta(module_.getSig(name.replaceFirst("Delta", "")));
    }
    else if (name.contains("Xi")) {
      ret = addXi(module_.getSig(name.replaceFirst("Xi", "")));
    }
    //		else if (fields_.containsKey(name)) {
    //			System.out.println("field");
    //			ret = new ExprVar(name, fields_.get(name));
    //		}
    else if (macros_.containsKey(name)) {
      ret = macros_.get(name);
    }
    else {
      AlloyExpr type = visit(refExpr.getAnn(TypeAnn.class));
      ret = new ExprVar(print(refExpr.getZName()), type);
    }
    ret = processRelation(ret, refExpr);
    return ret;
  }

  /** Ignore rules. */
  public AlloyExpr visitRule(Rule r) {
    return null;
  }

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

  /**
   * creates a new signiture to represent the schema <br>
   * includes all the fields of the schema <br>
   * if the schema contains an InclDecl, it includes all the fields of this
   * schema <br>
   * the predicate for this schema is included in the new signiture <br>
   * eg
   * 
   * <pre>
   * given sig A {a : univ}{pred_A[a]} pred pred_A[a] {...}
   * 
   * \begin{schema}{B}
   *  A 
   *  c : C
   * \where
   *  ...
   * \end{schema}
   *</pre>
   * 
   * translates to:
   * 
   * <pre>
   * sig B {a : univ, c : C} {pred_B[a,c]} pred pred_B {... and pred_A[a]}
   * </pre>
   * 
   */
  public AlloyExpr visitSchExpr(SchExpr schExpr) {
    String schName = names.get(schExpr);
    if (schName == null) {
      System.err.println("SchExprs must have names");
      throw new RuntimeException();
    }
    Sig sig = new PrimSig(schName);
    AlloyExpr fieldPred = null;
    for (Decl d : schExpr.getZSchText().getZDeclList()) {
      if (d instanceof VarDecl) {
        VarDecl vardecl = (VarDecl) d;
        ZNameList nameList = vardecl.getName();
        for (Name name : nameList) {
          sig.addField(new Field(print(name),
              visit(vardecl.getExpr())));
        }
      } else if (d instanceof InclDecl) {
        InclDecl incdecl = (InclDecl) d;
        AlloyExpr sigfieldpred = processSigField((Sig) visit(incdecl.getExpr()),
            sig);
        if (fieldPred != null) {
          fieldPred = fieldPred.and(sigfieldpred);
        } else {
          fieldPred = sigfieldpred;
        }
      } else {
        System.err.println(d.getClass() + " not yet implemented");
        throw new RuntimeException();
      }
    }
    addSig(sig);
    body = true;
    AlloyExpr pred = visit(schExpr.getZSchText().getPred());
    body = false;
    if (fieldPred != null) {
      addSigPred(sig, fieldPred);
    }
    if (pred != null) {
      addSigPred(sig, pred);
    }
    return null;
  }

  /**
   * <pre>
   * {expr1, ..., exprn @ pred}
   * </pre>
   * 
   * translates to
   * 
   * <pre>
   * {expr1, ..., exprn | pred}
   * </pre>
   * 
   * using visit to recursively translate the exprs and pred
   * 
   * @return the expression
   * 
   */
  public AlloyExpr visitSetCompExpr(SetCompExpr setCompExpr) {
    ExprVar firstVar = (ExprVar) visit(setCompExpr.getZSchText()
        .getZDeclList());
    List<ExprVar> rest = vars_;
    AlloyExpr pred = visit(setCompExpr.getZSchText().getPred());
    AlloyExpr oPred = visit(setCompExpr.getExpr());
    vars_.add(firstVar);
    if (pred == null) {
      pred = ExprConstant.TRUE;
    }
    if (oPred == null) {
      return pred.comprehensionOver(rest);
    }
    AlloyExpr type = visit(setCompExpr.getExpr().getAnn(TypeAnn.class));
    ExprVar exprVar = new ExprVar("temp", type);
    List<ExprVar> temp = new ArrayList<ExprVar>();
    temp.add(exprVar);
    return new ExprQuant(ExprQuant.Op.COMPREHENSION,
        temp,
        pred.and(new ExprQuant(ExprQuant.Op.SOME,
            vars_,
            oPred.equal(exprVar))));
  }

  /**
   * if the set is null or empty translates it to none <br/>
   * if the set has one member, transates it to that member <br/>
   * otherwise translates the set into th union of all its members <br/>
   * eg
   * 
   * <pre>
   * {a, b, c} =&gt; a + b + c
   * {a} =&gt; a
   * {} =&gt; none
   * </pre>
   */
  public AlloyExpr visitSetExpr(SetExpr setExpr) {
    if (setExpr.getExprList() == null) {
      return NONE;
    }
    ZExprList exprs = setExpr.getZExprList();
    if (exprs.size() == 0) {
      return NONE;
    } else if (exprs.size() == 1) {
      AlloyExpr ret = visit(exprs.get(0));
      return ret;
    } else {
      AlloyExpr expr = null;
      for (Expr e : exprs) {
        AlloyExpr ve = visit(e);
        if (ve == null) {
          System.err.println("Elements of setexpr must not be null");
          throw new RuntimeException();
        }
        if (expr == null) {
          expr = ve;
        } else {
          expr = expr.plus(ve);
        }
      }
      return expr;
    }
  }

  public AlloyExpr visitThetaExpr(ThetaExpr thetaExpr) {
    AlloyExpr expr = visit(thetaExpr.getExpr());
    if (! (expr instanceof Sig)) {
      System.err.println("not translated");
      throw new RuntimeException();
    }
    Sig sig = (Sig) expr;
    String strokes = "";
    for (Stroke s : thetaExpr.getZStrokeList()) {
      strokes+= printVisitor_.visitStroke(s);
    }
    ExprVar exprVar = new ExprVar(sig.label().toLowerCase() + strokes, sig);

    for (ExprVar ev : thetaQuantified) {
      if (ev.label().equals(exprVar.label())) {
        return ev;
      }
    }
    thetaQuantified.add(exprVar);
    AlloyExpr pred = null;
    for (Field f : sig.fields()) {
      if (pred == null) {
        pred = exprVar.join(f).equal(new ExprVar(f.label() + strokes,
            f.expr()));
      }
      else {
        pred = pred.and(exprVar.join(f).equal(new ExprVar(f.label() + strokes,
            f.expr())));
      }
    }
    if (thetaPred == ExprConstant.TRUE || thetaPred == null) {
      thetaPred = pred;
    }
    else {
      thetaPred = thetaPred.and(pred);
    }
    return exprVar;
  }

  public AlloyExpr visitTruePred(TruePred arg0) {
    return ExprConstant.TRUE;
  }

  public AlloyExpr visitTupleExpr(TupleExpr tupleExpr) {
    return visit(tupleExpr.getZExprList());
  }

  public AlloyExpr visitTypeAnn(TypeAnn typeAnn) {
    return visit(typeAnn.getType());
  }

  /**
   * creates a exprvar with the name and expr of the vDecl
   */
  public AlloyExpr visitVarDecl(VarDecl vDecl) {
    return new ExprVar(print(vDecl.getName()), visit(vDecl.getExpr()));
  }

  /**
   * uses visit to recursively translate the elements fo the ZDeclList <br/>
   * sets internally a list containing translations all elements other than
   * the first, in order
   * 
   * @return the first element
   */
  public AlloyExpr visitZDeclList(ZDeclList zDeclList) {
    Iterator<Decl> iter = zDeclList.iterator();
    AlloyExpr result = visit(iter.next());
    if (iter.hasNext()) {
      List<ExprVar> list = new ArrayList<ExprVar>();
      while (iter.hasNext()) {
        list.add((ExprVar) visit(iter.next()));
      }
      vars_ = list;
    } else {
      vars_ = new ArrayList<ExprVar>();
    }
    return result;
  }

  public AlloyExpr visitZExprList(ZExprList zExprList) {
    Iterator<Expr> iter = zExprList.iterator();
    AlloyExpr result = visit(iter.next());
    if (iter.hasNext()) {
      List<AlloyExpr> list = new ArrayList<AlloyExpr>();
      while (iter.hasNext()) {
        list.add(visit(iter.next()));
      }
      exprs_ = list;
    } else {
      exprs_ = new ArrayList<AlloyExpr>();
    }
    return result;
  }

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

  /**
   * This method is a helper method for visitAndExpr/visitOrExpr/visitIffExpr/visitImpliesExpr
   * 
   * The general idea is that there is an expression like: A \land B
   * 
   * This should return (pred_A[...], pred_B[...]
   * 
   * It gets a bit more complicated with more complex expressions, eg (A \land B) \lor C
   * 
   * In this case, the left side is handled recursively, and the right side by this method.
   * 
   * This relies on the the recursive call returning an expression in the form given above
   */
  private Pair<AlloyExpr, AlloyExpr> schExpr2SigComponent(SchExpr2 schExpr2) {
    // there are 2 options for this recursion.
    // either it is a sub expression (A Op B) - this is done
    // or it is a base case (A) - not done 
    // if it is a base case it should be a PrimSig, which needs to transform into 
    // the predicate call
    AlloyExpr left = visit(schExpr2.getLeftExpr());
    AlloyExpr right = visit(schExpr2.getRightExpr());
    if (left instanceof PrimSig) {
      PrimSig leftsig = (PrimSig) left;
      left = callSigPred(leftsig);
    }
    if (right instanceof PrimSig) {
      PrimSig rightsig = (PrimSig) right;
      right = callSigPred(rightsig);
    }
    if (left == null || right == null) {
      System.err.println("left and right of SchExpr2 must not be null");
      throw new RuntimeException();
    }
    return new Pair<AlloyExpr,AlloyExpr>(left, right );
  }

  /**
   * utility method
   * 
   * given a sig:
   * 
   * sig X {
   *    x1 : X1,
   *    ...,
   *    xn : Xn
   * } { pred_X[x1,...,xn] }
   * 
   * 
   * makes the call
   * 
   * pred_X[x1, ..., xn]
   * 
   * it is useful, but cheating because it only works if the variables needed
   * exactly match the names in the signature declaration
   */
  private AlloyExpr callSigPred(PrimSig sig) {
    Func leftPred = module_.getFunc("pred_" + sig.label());
    // this makes new exprvars for each field from the signature
    List<AlloyExpr> content = new ArrayList<AlloyExpr>();
    for (Field f : sig.fields()) {
      AlloyExpr fieldExpr = f;
      fieldExpr = new ExprVar(f.label(), fieldExpr);
      content.add(fieldExpr);
    }
    AlloyExpr[] args = content.toArray(new AlloyExpr[0]);
    return leftPred.call(args);
  }

  private AlloyExpr processSigField(Sig sigField, Sig sig) {
    // so we can easily see if a field is already present
    Map<String, Field> sigfieldnames = new HashMap<String, Field>();
    List<AlloyExpr> args = new ArrayList<AlloyExpr>();
    for (Field sigfield : sig.fields()) {
      sigfieldnames.put(sigfield.label(), sigfield);
    }
    for (Field subfield : sigField.fields()) {
      if (!sigfieldnames.containsKey(subfield.label())) {
        Field newfield = new Field(subfield.label(), subfield.expr());
        sig.addField(newfield);
        sigfieldnames.put(newfield.label(), newfield);
      }
      Field field = sigfieldnames.get(subfield.label());
      args.add(new ExprVar(field.label(), field.expr()));
    }
    Func f;
    if (module_.containsFunc("pred_" + sigField.label())) {
      f = module_.getFunc("pred_" + sigField.label());
    }
    else if (module_.containsFunc("pred_" + sigField.label().replaceAll("'", ""))) {
      f = module_.getFunc("pred_" + sigField.label().replace("'", ""));
    }
    else {
      return null;
    }
    return f.call(args.toArray(new AlloyExpr[0]));
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
      stack.push(t);
      AlloyExpr e = t.accept(this);
      stack.pop();
      return e;
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
  private List<Field> fields(SchExpr2 schExpr2) {
    Map<String, AlloyExpr> fields = new HashMap<String, AlloyExpr>();
    Queue<SchExpr2> subexprs = new LinkedList<SchExpr2>();
    subexprs.offer((SchExpr2) schExpr2);
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
      // TODO clare wtf is this for?
      fields_.put(f.label(), f.expr());
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
    // True and P = P, so get rid of True's here
    // it might be nice if this happened in the ast?
    if (existingPred.getBody() == ExprConstant.TRUE) {
      existingPred.setBody(pred);
    } else {
      existingPred.setBody(existingPred.getBody().and(pred));
    }
    //TODO clare fix this shit - something to do with theta I think
    if (! thetaQuantified.isEmpty()) {
      existingPred.setBody(new ExprQuant(ExprQuant.Op.SOME,
          thetaQuantified,
          existingPred.body().and(thetaPred)));
      thetaQuantified.clear();
      thetaPred = ExprConstant.TRUE;
    }
  }

  private void addField(Sig sig, Field field) {
    if (! sig.containsField(field.label())) {
      sig.addField(field);
    }
  }

  private Sig addDelta(Sig sig) {
    PrimSig delta = new PrimSig("Delta" + sig.label());
    List<AlloyExpr> preFields = new ArrayList<AlloyExpr>();
    List<AlloyExpr> postFields = new ArrayList<AlloyExpr>();
    for (Field field : sig.fields()) {
      Field pre = new Field(field.label(), field.expr());
      Field post = new Field(field.label() + "'", field.expr());
      delta.addField(pre);
      delta.addField(post);
      preFields.add(pre);
      postFields.add(post);
    }
    addSig(delta);
    Func pred = module_.getFunc("pred_" + sig.label());
    addSigPred(delta, pred.call(preFields));
    addSigPred(delta, pred.call(postFields));
    return delta;
  }

  private AlloyExpr addXi(Sig sig) {
    PrimSig xi = new PrimSig("Xi" + sig.label());
    List<AlloyExpr> preFields = new ArrayList<AlloyExpr>();
    List<AlloyExpr> postFields = new ArrayList<AlloyExpr>();

    for (Field field : sig.fields()) {
      Field pre = new Field(field.label(), field.expr());
      Field post = new Field(field.label() + "'", field.expr());
      xi.addField(pre);
      xi.addField(post);
      preFields.add(pre);
      postFields.add(post);
    }
    addSig(xi);
    for (int i = 0; i < xi.fields().size(); i += 2) {
      Field field1 = xi.fields().get(i);
      Field field2 = xi.fields().get(i + 1);
      addSigPred(xi, new ExprVar(field1.label(), field1.expr())
      .equal(new Field(field2.label(), field2.expr())));
    }
    Func pred = module_.getFunc("pred_" + sig.label());
    addSigPred(xi, pred.call(preFields));
    addSigPred(xi, pred.call(postFields));
    return xi;
  }

  private AlloyExpr build(AlloyExpr expr, Map<String, AlloyExpr> vars) {
    if (expr instanceof ExprCall) {
      // not sure exactly when and why these
      // are sometimes sigs and sometimes
      // preds
      expr = (module_.getSig(((ExprCall) expr).fun().label().replaceFirst("pred_", "")));
    }
    if (expr instanceof Sig) {
      Sig signiture = (Sig) expr;
      AlloyExpr[] exprs = new AlloyExpr[signiture.fields().size()];
      for (int i = 0; i < signiture.fields().size(); i++) {
        exprs[i] = vars.get(signiture.fields().get(i).label());
      }
      return module_.getFunc("pred_" + signiture.label()).call(exprs);
    }
    // should put in new kinds of things as they are needed
    System.err.println("Not fully translated: " + expr.getClass() + " "
        + expr);
    throw new RuntimeException();
  }


  /*
   * TODO Clare: make this actually work properly in all cases (maybe
   * this should be in the AST?)
   */
  private int arity(AlloyExpr expr) {
    if (expr instanceof ExprBinary && ((ExprBinary) expr).op().isArrow) {
      ExprBinary exprBinary = (ExprBinary) expr;
      return 1 + arity(exprBinary.left()) + arity(exprBinary.right());
    }
    if (expr instanceof ExprUnary) {
      return arity(((ExprUnary) expr).sub());
    }
    if (expr instanceof ExprVar) {
      return arity(((ExprVar) expr).expr());
    }
    return 1;
  }

  private AlloyExpr processRelation(AlloyExpr expr1, Expr expr2) {
    if (! body) return expr1;
    AlloyExpr t = visit(expr2.getAnn(TypeAnn.class));
    while  (t instanceof ExprUnary &&
        (((ExprUnary) t).op().equals(ExprUnary.Op.SETOF))) {
      t = ((ExprUnary) t).sub();
    }
    if (relationMap_.contains(t)) {
      Sig s = (Sig) t;
      return expr1.join(s.field(s.label().toLowerCase()));
    }
    return expr1;
  }

  private void debug(Term t) {
    StringWriter foo = new StringWriter();
    PrintUtils.print(t, foo, manager_, section_, Markup.UNICODE);
    System.out.println("Debug: " + foo);
  }

  class AlloyPrintVisitor extends PrintVisitor implements
  DecorExprVisitor<String>, RefExprVisitor<String>, StrokeVisitor<String> {
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

    public String visitInStroke(InStroke inStroke) {
      return "_in";
    }

    public String visitNextStroke(NextStroke nextStroke) {
      return "'";
    }

    public String visitOutStroke(OutStroke outStroke) {
      return "_out";
    }

    public String visitNumStroke(NumStroke numStroke) {
      return numStroke.getDigit().toString();
    }

    public String visitDecorExpr(DecorExpr decorExpr) {
      return decorExpr.getExpr().accept(this)
      + decorExpr.getStroke().accept(this);
    }

    public String visitRefExpr(RefExpr refExpr) {
      return refExpr.getName().accept(this);
    }

    @Override
    public String visitStroke(Stroke stroke) {
      return stroke.accept(this);
    }
  }
}
