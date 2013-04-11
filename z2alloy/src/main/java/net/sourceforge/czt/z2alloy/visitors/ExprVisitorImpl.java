package net.sourceforge.czt.z2alloy.visitors;

import static net.sourceforge.czt.z2alloy.ast.Sig.NONE;
import static net.sourceforge.czt.z2alloy.ast.Sig.SIGINT;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.BindSelExpr;
import net.sourceforge.czt.z.ast.CompExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.HideExpr;
import net.sourceforge.czt.z.ast.IffExpr;
import net.sourceforge.czt.z.ast.ImpliesExpr;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.BindSelExprVisitor;
import net.sourceforge.czt.z.visitor.CompExprVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.HideExprVisitor;
import net.sourceforge.czt.z.visitor.IffExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesExprVisitor;
import net.sourceforge.czt.z.visitor.LambdaExprVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.OrExprVisitor;
import net.sourceforge.czt.z.visitor.PowerExprVisitor;
import net.sourceforge.czt.z.visitor.ProdExprVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SetCompExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprBinary;
import net.sourceforge.czt.z2alloy.ast.ExprCall;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;
import net.sourceforge.czt.z2alloy.ast.ExprQuant;
import net.sourceforge.czt.z2alloy.ast.ExprUnary;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;

public class ExprVisitorImpl extends ExprVisitorAbs implements
ExprVisitor<AlloyExpr>,
AndExprVisitor<AlloyExpr>,
ApplExprVisitor<AlloyExpr>,
BindSelExprVisitor<AlloyExpr>,
CompExprVisitor<AlloyExpr>,
DecorExprVisitor<AlloyExpr>,
HideExprVisitor<AlloyExpr>,
IffExprVisitor<AlloyExpr>,
ImpliesExprVisitor<AlloyExpr>,
LambdaExprVisitor<AlloyExpr>,
NumExprVisitor<AlloyExpr>,
OrExprVisitor<AlloyExpr>,
PowerExprVisitor<AlloyExpr>,
ProdExprVisitor<AlloyExpr>,
RefExprVisitor<AlloyExpr>,
SchExprVisitor<AlloyExpr>,
SetCompExprVisitor<AlloyExpr>,
SetExprVisitor<AlloyExpr>,
ThetaExprVisitor<AlloyExpr>
{
  
  public ExprVisitorImpl(PredVisitorAbs pred) {
    super(pred);
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
   * ran                          calls ran[right]
   * addition                     left + right
   * substraction                 left - right
   * dres                         left <: right
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
        String binOp = Z2Alloy.isInfixOperator(refExpr.getZName());
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
        else if (binOp.equals(ZString.SETMINUS)) {
          ret = left.minus(right);
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
          if (Z2Alloy.getInstance().module().containsFunc("ndres"))
            ret = Z2Alloy.getInstance().module().getFunc("ndres").call(args);
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
          if (Z2Alloy.getInstance().module().containsFunc("append"))
            ret = Z2Alloy.getInstance().module().getFunc("append").call(left, right);
        }
        else if (binOp.equals(ZString.MINUS)) {
          if (Z2Alloy.getInstance().module().containsFunc("sub")) {
            ret = Z2Alloy.getInstance().module().getFunc("sub").call(left, right);
          }
        }
        else if (binOp.equals(ZString.PLUS)) {
          if (Z2Alloy.getInstance().module().containsFunc("add")) {
            ret = Z2Alloy.getInstance().module().getFunc("add").call(left, right);
          }
        }
        else if (binOp.equals(ZString.MULT)) {
          if (Z2Alloy.getInstance().module().containsFunc("mul")) {
            ret = Z2Alloy.getInstance().module().getFunc("mul").call(left, right);
          }
        }
        else if (binOp.equals("div")) {
          if (Z2Alloy.getInstance().module().containsFunc("div")) {
            ret = Z2Alloy.getInstance().module().getFunc("div").call(left, right);
          }
        }
        else if (binOp.equals("mod")) {
          if (Z2Alloy.getInstance().module().containsFunc("rem")) {
            ret = Z2Alloy.getInstance().module().getFunc("rem").call(left, right);
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
        if (Z2Alloy.getInstance().print(refExpr.getName()).equals(ZString.LANGLE + " ,, " + ZString.RANGLE)) { // sequence
          if (body == NONE) {
            ret = NONE.product(NONE);
          } else {
            System.err.println("non empty sequences not translated yet");
            throw new RuntimeException();
          }
        }
        else if (Z2Alloy.getInstance().print(refExpr.getName()).equals("# _ ")) {
          ret = body.cardinality();
        }
        else if (Z2Alloy.getInstance().print(refExpr.getName()).equals("- _ ")) {
          if (Z2Alloy.getInstance().module().containsFunc("negate"))
            ret = Z2Alloy.getInstance().module().getFunc("negate").call(body);
        }
        else if (Z2Alloy.getInstance().print(refExpr.getName()).equals("succ _ ")) {
          if (Z2Alloy.getInstance().module().containsFunc("next"))
            ret = Z2Alloy.getInstance().module().getFunc("next").call(body);
        }
      }
    }
    else { // application
      if (applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        String name = Z2Alloy.getInstance().print(refExpr.getName());
        if (name.equals("dom")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (Z2Alloy.getInstance().module().containsFunc("dom"))
            ret = Z2Alloy.getInstance().module().getFunc("dom").call(body);
        }
        else if (name.equals("ran")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (Z2Alloy.getInstance().module().containsFunc("ran")) 
            ret = Z2Alloy.getInstance().module().getFunc("ran").call(body);
        }
        else if (name.equals("last")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (Z2Alloy.getInstance().module().containsFunc("last"))
            ret = Z2Alloy.getInstance().module().getFunc("last").call(body);
        }
        else if (name.equals("front")) {
          AlloyExpr body = visit(applExpr.getRightExpr());
          if (Z2Alloy.getInstance().module().containsFunc("front"))
            ret = Z2Alloy.getInstance().module().getFunc("front").call(body);
        }
        else if (Z2Alloy.getInstance().module().containsFunc(Z2Alloy.getInstance().print(refExpr.getZName()))) {
          Func fun = Z2Alloy.getInstance().module().getFunc(Z2Alloy.getInstance().print(refExpr.getZName()));
          if (applExpr.getRightExpr() instanceof TupleExpr) {
            List<AlloyExpr> right = new TupleExprVisitorImpl(pred()).visitTupleExpr((TupleExpr) applExpr.getRightExpr());
            ret = fun.call(right);
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
  
  // TODO figure out wtf this is supposed to be
  public AlloyExpr visitBindSelExpr(BindSelExpr bindSelExpr) {
    AlloyExpr left = visit(bindSelExpr.getExpr());
    ExprVar right = new ExprVar(Z2Alloy.getInstance().print(bindSelExpr.getName()));
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
      if (! Z2Alloy.getInstance().module().containsSig(name)) {
        System.err.println("not translated");
        throw new RuntimeException();
      }
      Sig quant = Z2Alloy.getInstance().module().getSig(name);
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
      Func predleft = Z2Alloy.getInstance().module().getFunc("pred_" + left.label());
      Func predRight = Z2Alloy.getInstance().module().getFunc("pred_" + right.label());
      return predleft.call(vars1).and(predRight.call(vars2)).forSome(vars);
    }
    else {
      System.err.println("not implemented");
      throw new RuntimeException();
    }
  }
  
  public AlloyExpr visitDecorExpr(DecorExpr decorExpr) {
    AlloyExpr expr = visit(decorExpr.getExpr());
    if (expr instanceof Sig) {
      Sig sig = (Sig) expr;
      Sig sigStroke = new PrimSig(sig.label() + Z2Alloy.getInstance().print(decorExpr.getStroke()));
      for (Field field : sig) {
        sigStroke.addField(new Field(field.label()
            + Z2Alloy.getInstance().print(decorExpr.getStroke()),
            field.expr()));
      }
      return sigStroke;
    }
    else {
      System.err.println("not yet translated");
      throw new RuntimeException();
    }
  }
  
  public AlloyExpr visitHideExpr(HideExpr hideExpr) {
    Sig newSig = new PrimSig(Z2Alloy.getInstance().names().get(hideExpr));
    List<String> hiddenNames = new ArrayList<String>();
    for (Name n : hideExpr.getZNameList()) hiddenNames.add(Z2Alloy.getInstance().print(n));
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
      fields = Z2Alloy.getInstance().fields(schExpr2);
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
    Z2Alloy.getInstance().addSig(newSig);
    Z2Alloy.getInstance().addSigPred(newSig, new ExprQuant(ExprQuant.Op.SOME, hidden, sub));
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
  
  public AlloyExpr visitLambdaExpr(LambdaExpr lambda) {
    String name = Z2Alloy.getInstance().names().get(lambda);
    if (Z2Alloy.getInstance().module().containsFunc(name)) return null;
    List<AlloyExpr> vars = new ZDeclListVisitorImpl().visitZDeclList(lambda.getZSchText().getZDeclList());
    List<ExprVar> vars2 = new ArrayList<ExprVar>();
    for (AlloyExpr alloyExpr : vars) {
      if (alloyExpr instanceof ExprVar) {
        vars2.add((ExprVar) alloyExpr);
      }
    }
    Z2Alloy.getInstance().body = true;
    AlloyExpr body = visit(lambda.getExpr());
    Z2Alloy.getInstance().body = false;
    TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
    AlloyExpr returnDecl = visit(type);
    ExprVar j = new ExprVar("j", returnDecl);
    vars.add(j);
    ExprQuant exprQuant =
      new ExprQuant(ExprQuant.Op.COMPREHENSION, vars2, j.equal(body)); 
    return exprQuant;
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
  
  /**
   * recursively calls visit on the sub expression and creates an alloy set of
   * the translation
   * 
   * @return the expression or null if the sub expression translates to null
   */
  public AlloyExpr visitPowerExpr(PowerExpr powerExpr) {
    AlloyExpr body = visit(powerExpr.getExpr());
    if (body == null) {
      System.err.println("Z2Alloy.getInstance().body of power expr must not be null");
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
        System.err.println("Z2Alloy.getInstance().body of prodexprs must not be  null");
        throw new RuntimeException();
      }
      expr = expr.product(current);
    }
    return expr;
  }
 
  /**
   * kinds of RefExpr translated: <br>
   * subexprs are translated recursively using visit
   * 
   * <pre>
   * pfun               expr0 -&gt; lone expr1
   * rel                  expr0 -&gt; expr1
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
    String name = Z2Alloy.getInstance().print(refExpr.getName());
    AlloyExpr ret = null;
    if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.PFUN)) {
      ret = Z2Alloy.getInstance().relationMap().createPFun(visit(refExpr.getZExprList().get(0)),
          visit(refExpr.getZExprList().get(1)));
    }
    else if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.REL)) {
      ret = Z2Alloy.getInstance().relationMap().create(visit(refExpr.getZExprList().get(0)),
          visit(refExpr.getZExprList().get(1)));
    }
    else if (Z2Alloy.isPostfixOperator(refExpr.getZName(), "seq")) {
      ret = Z2Alloy.getInstance().relationMap().createSeq(visit(refExpr.getZExprList().get(0)));
    }
    else if (Z2Alloy.getInstance().print(refExpr.getZName()).equals(ZString.ARITHMOS)) {
      ret = SIGINT;
    }
    else if (Z2Alloy.getInstance().print(refExpr.getZName()).equals(ZString.NAT)) {
      ExprVar i = new ExprVar("i", SIGINT);
      AlloyExpr sub = i.gte(ExprConstant.ZERO);
      List<ExprVar> vars = new ArrayList<ExprVar>();
      vars.add(i);
      ret = sub.comprehensionOver(vars);
    }
    else if (Z2Alloy.getInstance().print(refExpr.getZName()).equals(ZString.NUM)) {
      ret = SIGINT;
    }
    else if (Z2Alloy.getInstance().print(refExpr.getZName()).equals(ZString.EMPTYSET)) {
      AlloyExpr type = visit(refExpr.getAnn(TypeAnn.class));
      int num = arity(type);
      ret = NONE;
      for (int i = 1; i < num; i++) ret = NONE.product(NONE);
    }
    else if (Z2Alloy.getInstance().module().containsSig(name)) {
      ret = Z2Alloy.getInstance().module().getSig(name);
    }
    else if (name.contains("Delta")
        && Z2Alloy.getInstance().module().containsSig(name.replaceFirst("Delta", ""))) {
      ret = addDelta(Z2Alloy.getInstance().module().getSig(name.replaceFirst("Delta", "")));
    }
    else if (name.contains("Xi")) {
      ret = addXi(Z2Alloy.getInstance().module().getSig(name.replaceFirst("Xi", "")));
    }
    //      else if (fields_.containsKey(name)) {
    //          System.out.println("field");
    //          ret = new ExprVar(name, fields_.get(name));
    //      }
    else if (Z2Alloy.getInstance().macros().containsKey(name)) {
      ret = Z2Alloy.getInstance().macros().get(name);
    }
    else {
      AlloyExpr type = visit(refExpr.getAnn(TypeAnn.class));
      ret = new ExprVar(Z2Alloy.getInstance().print(refExpr.getZName()), type);
    }
    ret = processRelation(ret, refExpr);
    return ret;
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
    String schName = Z2Alloy.getInstance().names().get(schExpr);
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
          sig.addField(new Field(Z2Alloy.getInstance().print(name),
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
    Z2Alloy.getInstance().addSig(sig);
    Z2Alloy.getInstance().body = true;
    AlloyExpr pred = visit(schExpr.getZSchText().getPred());
    Z2Alloy.getInstance().body = false;
    if (fieldPred != null) {
      Z2Alloy.getInstance().addSigPred(sig, fieldPred);
    }
    if (pred != null) {
      Z2Alloy.getInstance().addSigPred(sig, pred);
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
    List<AlloyExpr> rest = new ZDeclListVisitorImpl().visitZDeclList(setCompExpr.getZSchText().getZDeclList());
    List<ExprVar> vars2 = new ArrayList<ExprVar>();
    for (AlloyExpr alloyExpr : rest) {
      if (alloyExpr instanceof ExprVar) {
        vars2.add((ExprVar) alloyExpr);
      }
    }
    AlloyExpr pred = visit(setCompExpr.getZSchText().getPred());
    AlloyExpr oPred = visit(setCompExpr.getExpr());
    if (pred == null) {
      pred = ExprConstant.TRUE;
    }
    if (oPred == null) {
      return pred.comprehensionOver(vars2);
    }
    AlloyExpr type = visit(setCompExpr.getExpr().getAnn(TypeAnn.class));
    ExprVar exprVar = new ExprVar("temp", type);
    List<ExprVar> temp = new ArrayList<ExprVar>();
    temp.add(exprVar);
    return new ExprQuant(ExprQuant.Op.COMPREHENSION,
        temp,
        pred.and(new ExprQuant(ExprQuant.Op.SOME,
            vars2,
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
//    for (Stroke s : thetaExpr.getZStrokeList()) {
 //     strokes+= Z2Alloy.getInstance().printVisitor().visitStroke(s);
  //  }
    ExprVar exprVar = new ExprVar(sig.label().toLowerCase() + strokes, sig);
    
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
    theta(exprVar, pred);
    return exprVar;
  }

  private AlloyExpr processRelation(AlloyExpr expr1, Expr expr2) {
    if (! Z2Alloy.getInstance().body) return expr1;
    AlloyExpr t = visit(expr2.getAnn(TypeAnn.class));
    while  (t instanceof ExprUnary &&
        (((ExprUnary) t).op().equals(ExprUnary.Op.SETOF))) {
      t = ((ExprUnary) t).sub();
    }
    if (Z2Alloy.getInstance().relationMap().contains(t)) {
      Sig s = (Sig) t;
      return expr1.join(s.field(s.label().toLowerCase()));
    }
    return expr1;
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
    Z2Alloy.getInstance().addSig(xi);
    for (int i = 0; i < xi.fields().size(); i += 2) {
      Field field1 = xi.fields().get(i);
      Field field2 = xi.fields().get(i + 1);
      Z2Alloy.getInstance().addSigPred(xi, new ExprVar(field1.label(), field1.expr())
      .equal(new Field(field2.label(), field2.expr())));
    }
    Func pred = Z2Alloy.getInstance().module().getFunc("pred_" + sig.label());
    Z2Alloy.getInstance().addSigPred(xi, pred.call(preFields));
    Z2Alloy.getInstance().addSigPred(xi, pred.call(postFields));
    return xi;
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
    Z2Alloy.getInstance().addSig(delta);
    Func pred = Z2Alloy.getInstance().module().getFunc("pred_" + sig.label());
    Z2Alloy.getInstance().addSigPred(delta, pred.call(preFields));
    Z2Alloy.getInstance().addSigPred(delta, pred.call(postFields));
    return delta;
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
    if (Z2Alloy.getInstance().module().containsFunc("pred_" + sigField.label())) {
      f = Z2Alloy.getInstance().module().getFunc("pred_" + sigField.label());
    }
    else if (Z2Alloy.getInstance().module().containsFunc("pred_" + sigField.label().replaceAll("'", ""))) {
      f = Z2Alloy.getInstance().module().getFunc("pred_" + sigField.label().replace("'", ""));
    }
    else {
      return null;
    }
    return f.call(args.toArray(new AlloyExpr[0]));
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
    return Pair.getPair(left, right );
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
    Func leftPred = Z2Alloy.getInstance().module().getFunc("pred_" + sig.label());
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
  
}
