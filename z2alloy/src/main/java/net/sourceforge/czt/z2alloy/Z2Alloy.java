/**
Copyright (C) 2008 Petra Malik, Clare Lenihan
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

import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.NONE;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SEQIDX;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SIGINT;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.UNIV;
import static net.sourceforge.czt.z.util.ZUtils.assertZBranchList;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
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
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.BindSelExpr;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.IffExpr;
import net.sourceforge.czt.z.ast.ImpliesExpr;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BindSelExprVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.Exists1PredVisitor;
import net.sourceforge.czt.z.visitor.ExistsExprVisitor;
import net.sourceforge.czt.z.visitor.ExistsPredVisitor;
import net.sourceforge.czt.z.visitor.ForallPredVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.IffExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.OrExprVisitor;
import net.sourceforge.czt.z.visitor.OrPredVisitor;
import net.sourceforge.czt.z.visitor.PowerExprVisitor;
import net.sourceforge.czt.z.visitor.PowerTypeVisitor;
import net.sourceforge.czt.z.visitor.ProdExprVisitor;
import net.sourceforge.czt.z.visitor.ProdTypeVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SchemaTypeVisitor;
import net.sourceforge.czt.z.visitor.SetCompExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.TypeAnnVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.visitor.RuleVisitor;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQuant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;


public class Z2Alloy
implements TermVisitor<Expr>,
AndExprVisitor<Expr>,
AndPredVisitor<Expr>,
ApplExprVisitor<Expr>,
AxParaVisitor<Expr>,
BindSelExprVisitor<Expr>,
ExistsExprVisitor<Expr>,
Exists1PredVisitor<Expr>,
ExistsPredVisitor<Expr>,
ForallPredVisitor<Expr>,
FreeParaVisitor<Expr>,
FreetypeVisitor<Expr>,
GivenParaVisitor<Expr>,
GivenTypeVisitor<Expr>,
IffExprVisitor<Expr>,
ImpliesExprVisitor<Expr>,
ImpliesPredVisitor<Expr>,
LatexMarkupParaVisitor<Expr>,
MemPredVisitor<Expr>,
NarrParaVisitor<Expr>,
NumExprVisitor<Expr>,
OrExprVisitor<Expr>,
OrPredVisitor<Expr>,
PowerExprVisitor<Expr>,
PowerTypeVisitor<Expr>,
ProdExprVisitor<Expr>,
ProdTypeVisitor<Expr>,
RefExprVisitor<Expr>,
RuleVisitor<Expr>,
SchemaTypeVisitor<Expr>,
SchExprVisitor<Expr>,
SetCompExprVisitor<Expr>,
SetExprVisitor<Expr>,
TupleExprVisitor<Expr>,
TypeAnnVisitor<Expr>,
VarDeclVisitor<Expr>,
ZDeclListVisitor<Expr>,
ZFreetypeListVisitor<Expr>,
ZSectVisitor<Expr>
{
  private SectionManager manager_;
  private AlloyPrintVisitor printVisitor_ = new AlloyPrintVisitor();
  private String section_ = "z2alloy";
  private boolean unfolding_ = false;
  private ExprVar[] vars_;

  public Map<String, Sig> sigmap_ = new HashMap<String, Sig>();
  public List<Sig> sigOrder_ = new ArrayList<Sig>();
  public Map<Sig, Func> sigpreds_ = new HashMap<Sig,Func>();
  public Map<Sig, Expr> sigfacts_ = new HashMap<Sig, Expr>();
  private Map<Term, String> schemaName_ = new HashMap<Term, String>();
  public Map<String, Func> functions_ = new HashMap<String, Func>();
  private Map<String, Expr> fields_ = new HashMap<String, Expr>();

  // private Map<String, Expr> paramTypes_ = new HashMap<String, Expr>();

  /**
   * A mapping from ZName ids to alloy names.
   */
  private Map<String,String> names_ = new HashMap<String,String>();

  public Z2Alloy(SectionManager manager)
  throws Exception
  {
    manager_ = manager;
  }

  public void setUnfolding(boolean unfolding)
  {
    unfolding_ = unfolding;
  }

  //==================== Visitor Methods ==================

  public Expr visitTerm(Term term)       
  {      
    System.err.println(term.getClass() + " not yet implemented");        
    return null;         
  }

  /**
   * translates an and expression (schema conjunction) into an alloy and expression. The schemas are translated into a call to the
   * predicate translated by the schema
   * 
   * eg 
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \land B => pred_A[a] and pred_B[b]
   * </pre>
   * Currently the actual variables from the signiture are not used in the pred calls. Instead new ones are created. This works, assuming
   * the variables are declared with the same name as in the predicate declaration.
   * 
   * @return the expression
   */
  public Expr visitAndExpr(AndExpr andExpr)
  {
    Expr[] comps = schExpr2SigComponent(andExpr);
    return comps[0].and(comps[1]);
  }

  /**
   * translates an and predicate (ie conjunction) into an alloy and expression.The kind of conjunction used (newline, \and, chain)
   * does not change the result
   * 
   * left and right expressions are recurisvely translated using visit
   * 
   * @return the expression if it successfully translated, or null it something fails
   */
  public Expr visitAndPred(AndPred andPred)
  {
    Expr left = visit(andPred.getLeftPred());
    Expr right = visit(andPred.getRightPred());
    if (left == null || right == null) {
      System.err.println("left and right of andpred must not be null");
      return null;
    }
    return left.and(visit(andPred.getRightPred()));
  }

  /**
   * translates a function application
   * <br>
   * types of application expressions currently translated:
   * <pre>
   * union                      left + right
   * relational override        left ++ right
   * rightwards arrow from bar  left -> right
   * ndres                      calls ndres[left, right], creating the function if it does not already exist
   * implication                left => right
   * ..                         {i : Int | i >= left and i <= right}
   * dom                        calls dom[right], creating the function if it does not already exist
   * </pre>
   * otherwise tries left.right
   * @return the expression if it successfully translated, or null it something fails
   */
  public Expr visitApplExpr(ApplExpr applExpr)
  {
    if (applExpr.getMixfix()) {
      if (applExpr.getRightExpr() instanceof TupleExpr &&
          applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        String binOp = isInfixOperator(refExpr.getZName());
        ZExprList exprs = ((TupleExpr) applExpr.getRightExpr()).getZExprList();
        Expr left = visit(exprs.get(0));
        Expr right = visit(exprs.get(1));
        if (left == null || right == null) {
          System.err.println("left and right of a binary expression must not be null");
          return null;
        }
        if (binOp.equals(ZString.CUP)) {
          return left.plus(right);
        }
        if (binOp.equals(ZString.OPLUS)) {
          return left.override(right);
        }
        if (binOp.equals(ZString.MAPSTO)) {
          return left.product(right);
        }
        if (binOp.equals(ZString.NDRES)) {
          if (functions_.containsKey("ndres")) return functions_.get("ndres").call(left, right);
          try {
            List<ExprVar> vars = new ArrayList<ExprVar>();
            ExprVar r = ExprVar.make(null, "r", UNIV.product(UNIV));
            vars.add(r);
            Func dom = new Func(null, "dom", vars, UNIV.setOf());

            ExprVar ex = ExprVar.make(null, "ex", UNIV.setOf());
            r = ExprVar.make(null, "r", UNIV.product(UNIV));
            vars.clear();
            vars.add(ex);
            vars.add(r);
            Func ndres = new Func(null, "ndres", vars, UNIV.product(UNIV));
            dom.setBody(r.join(UNIV));
            ndres.setBody((dom.call(r)).minus(ex).domain(r));
            functions_.put(ndres.label, ndres);
            return ndres.call(left, right);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
        }
        if (binOp.equals(ZString.IMP)) {
          return left.implies(right);
        }
        if (binOp.equals("..")) {
          ExprVar i = ExprVar.make(null, "i", SIGINT);
          Expr pred = i.gte(left).and(i.lte(right));
          return pred.comprehensionOver(i, new ExprVar[0]);
        }
        if (binOp.equals(ZString.CAT)) {
//        currently uses the definition of append from util/sequniv.als
//        fun append [s1, s2: Int -> univ] : s1+s2 {
//        let shift = {i', i: seq/Int | int[i'] = int[i] + int[lastIdx[s1]] + 1 } |
//        no s1 => s2 else (s1 + shift.s2)
//        }

          try {
            ExprVar s1 = ExprVar.make(null, "s1", SIGINT.product(UNIV));
            ExprVar s2 = ExprVar.make(null, "s2", SIGINT.product(UNIV));
            List<ExprVar> vars = new ArrayList<ExprVar>();
            vars.add(s1);
            vars.add(s2);
            Expr res = s1.plus(s2);
            Func append = new Func(null, "seq/append", vars, res);
            return append.call(left, right);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
        }
        System.err.println(applExpr.getClass() + " not yet implemented");
        return null;
      }
    }
    else { // application
      if (applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        if (print(refExpr.getName()).equals("dom")) {
          Expr body = visit(applExpr.getRightExpr());
          if (functions_.containsKey("dom")) return functions_.get("dom").call(body);
          List<ExprVar> vars = new ArrayList<ExprVar>();
          ExprVar r = ExprVar.make(null, "r", UNIV.product(UNIV));
          vars.add(r);
          try {
            Func dom = new Func(null, "dom", vars, UNIV.setOf());
            dom.setBody(r.join(UNIV));
            functions_.put(dom.label, dom);
            return dom.call(body);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
        }
        if (print(refExpr.getName()).equals("last")) {
          // fun last [s: Int -> univ]: lone (Int.s) { s[lastIdx[s]] }
          Expr body = visit(applExpr.getRightExpr());
          ExprVar s = ExprVar.make(null, "s", SIGINT.product(UNIV));
          List<ExprVar> vars = new ArrayList<ExprVar>();
          vars.add(s);
          Expr ret = SIGINT.join(s).loneOf();
          try {
            Func last = new Func(null, "seq/last", vars, ret);
            return last.call(body);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
        }
        if (print(refExpr.getName()).equals("front")) {
          // seq/butlast is equivalent to front in Z
          // fun butlast [s: Int -> univ] : s {
          //   (seq/Int - lastIdx[s]) <: s
          // }
          Expr body = visit(applExpr.getRightExpr());
          ExprVar s = ExprVar.make(null, "s", SIGINT.product(UNIV));
          List<ExprVar> vars = new ArrayList<ExprVar>();
          vars.add(s);
          Expr ret = SIGINT.product(UNIV);
          try {
            Func butLast = new Func(null, "seq/butlast", vars, ret);
            return butLast.call(body);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
        }
        if (functions_.containsKey(print(refExpr.getZName()))) {
          Expr body = visit(applExpr.getRightExpr());
          return functions_.get(print(refExpr.getZName())).call(body);
        }
      }
    }
    Expr left = visit(applExpr.getLeftExpr());
    Expr right = visit(applExpr.getRightExpr());
    if (left == null || right == null) {
      System.err.println("left and right exprs must not be null in an ApplExpr");
      return null;
    }
    return right.join(left);
  }

  /**
   * If the para is a schema defined by a schema expression, it creates a new signiture which contains all the fields
   * of the translated sigs of the schemas in the expression. The precicate of the new sig is the result of recursively
   * calling visit on the schema expression, ie the expression created by visitAndExpr, visitOrExpr, etc.
   * 
   * eg for
   * <pre>
   *    A => sig A {a : univ}{pred_A[a]} pred pred_A[a:univ]{...}
   *    B => sig B {b : univ}{pred_B[b]} pred pred_B[b:univ]{...}
   *    C => sig C {c : univ}{pred_C[c]} pred pred_C[c:univ]{...}
   *  
   *    D == (A \land B) \lor C
   *    
   *  =>
   *    sig D {a : univ, b : univ, c : univ}{pred_D[a,b,b]} pred pred_D[a:univ,b:univ,c:univ]{(pred_A[a] and pred_B[b]) or pred_C[c]}
   *  </pre>
   *  @return null 
   *  
   *  
   */
  // TODO Other cases: RefExprs, LambdaExpr, just visit(result).
  public Expr visitAxPara(AxPara para)
  {
    if (para.getName().size() > 0) {
      System.err.println("Generic definitions not handled yet.");
      return null;
    }
    ZSchText schText = para.getZSchText();
    for (Decl decl : schText.getZDeclList()) {
      if (decl instanceof ConstDecl) {
        ConstDecl cDecl = (ConstDecl) decl;
        try {
          String sigName = print(cDecl.getName());
          net.sourceforge.czt.z.ast.Expr result = cDecl.getExpr();
          if (unfolding_) {
            Source exprSource =
              new StringSource("normalize~" +
                  print(cDecl.getName()));
            exprSource.setMarkup(Markup.LATEX);
            net.sourceforge.czt.z.ast.Expr toBeNormalized =
              ParseUtils.parseExpr(exprSource, section_, manager_);
            result = (net.sourceforge.czt.z.ast.Expr) preprocess(toBeNormalized);
            TypeCheckUtils.typecheck(result, manager_, false, section_);
          }
          if (result instanceof LambdaExpr) {
            String name = print(cDecl.getName());

            if (functions_.containsKey(name)) return null;
            LambdaExpr lambda = (LambdaExpr) result;
            List<ExprVar> vars = new ArrayList<ExprVar>();
            vars.add((ExprVar) visit(lambda.getZSchText().getZDeclList()));
            if (vars_ != null) {
              for (ExprVar exprVar : vars_) {
                vars.add(exprVar);
              }
            }
            Expr body = visit(lambda.getExpr());
            try {
              TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
              Expr returnDecl = visit(type);
              Func func = new Func(null, name, vars, returnDecl);
              if (body != null) func.setBody(body);
              functions_.put(func.label, func);
            }
            catch (Err e) {
              throw new RuntimeException(e);
            }
            return null;
          }
          schemaName_.put(result, sigName);
          if (result instanceof SchExpr2) {
            processSchExpr2((SchExpr2) result);
            return null;
          }
          return visit(result);
        }
        catch (CommandException e) {
          throw new RuntimeException(e);
        }
        catch (IOException e) {
          throw new RuntimeException(e);
        }
      }
    }
    System.err.println(para.getClass() + " not yet implemented");
    return null;
  }
  
  public Expr visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    Expr left = visit(bindSelExpr.getExpr());
    Iterator<Type.ProductType> entries = left.type.iterator();
    String lastName = null;
    while(entries.hasNext()) {
      lastName = entries.next().toString();
    }
    for (Sig.Field field : sigmap_.get(lastName).getFields()) {
      if (field.label.equals(print(bindSelExpr.getZName()))) {
        return left.join(field);
      }
    }
    return null;
  }
  
  /**
   * TODO Clare write the comments and explain this
   */
  public Expr visitExistsExpr(ExistsExpr existsExpr)
  {
    ZDeclList incl = existsExpr.getZSchText().getZDeclList();

    List<Sig> inclSigs = new ArrayList<Sig>();
    ExprVar[] inclVars = new ExprVar[incl.size() -1];

    Sig s = (Sig) visit(((InclDecl) incl.get(0)).getExpr());
    inclSigs.add(s);
    ExprVar first = (ExprVar.make(null, s.label.toLowerCase() + "_temp", s));      


    for (int i = 1; i < incl.size(); i++) {
      s = (Sig) visit(((InclDecl) incl.get(i)).getExpr());
      inclSigs.add(s);
      inclVars[i-1] = (ExprVar.make(null, s.label.toLowerCase() + "_temp", s));      
    }

    Expr pred = visit(existsExpr.getExpr());

    List<Sig> predSigs = new ArrayList<Sig>();
    Stack<Expr> predParts = new Stack<Expr>();
    predParts.add(pred);

    while (! predParts.isEmpty()) {
      Expr temp = predParts.pop();
      if (temp instanceof Sig) {
        predSigs.add((Sig) temp);
      }
      else if (temp instanceof ExprList) {
        predParts.addAll(((ExprList) temp).args);
      }
      else if (temp instanceof ExprCall) {
        predSigs.add(sigmap_.get(((ExprCall) temp).fun.label.replaceFirst("pred_", "")));
      }
      else {
        System.err.println("Not fully translated: " + temp.getClass() + " " + temp);
        return null;
      }
    }

    Map<String, Expr> fields = new HashMap<String, Expr>();
    for (Sig sig : predSigs) {
      for (Sig.Field field : sig.getFields()) {
        fields.put(field.label, getFieldExpr(field));

      }
    }
    for (int i = 0; i < inclSigs.size(); i++) {
      for (Sig.Field field : inclSigs.get(i).getFields()) {
        if (i == 0) {
          fields.put(field.label, first.join(field));
        }
        else{
          fields.put(field.label, inclVars[i-1].join(field));
        }
      }
    }

    PrimSig sig;
    try {
      sig = new PrimSig(null, schemaName_.get(existsExpr));
      for (Entry<String, Expr> field : fields.entrySet()) {
        sig.addField(null, field.getKey(), field.getValue());
      }
      addSig(sig);
      Expr predBody = build(pred, fields);

      Map<String, List<Expr>> dupFields = new HashMap<String, List<Expr>>();
      for (int i = 0; i < inclSigs.size(); i++) {
        for (Sig.Field field : inclSigs.get(i).getFields()) {
          if (!dupFields.containsKey(field.label)) {
            dupFields.put(field.label, new ArrayList<Expr>());
          }
          if (i == 0) {
            dupFields.get(field.label).add(first.join(field));
          }
          else{
            dupFields.get(field.label).add(inclVars[i-1].join(field));
          }
        }
      }

      for (Entry<String, List<Expr>> entry : dupFields.entrySet()) {
        for (int i = 1; i < entry.getValue().size(); i++) {
          if (predBody == null) {
            predBody = entry.getValue().get(0).equal(entry.getValue().get(i));
          }
          else {
            predBody = predBody.and(entry.getValue().get(0).equal(entry.getValue().get(i)));
          }
        }
      }

      addSigPred(sig, predBody.forSome(first, inclVars));

      return null;
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * uses visit to recursively translate variables and predicates.
   * 
   * <pre>\exists_1 var1, ... varn @ pred1 | pred2</pre> translates to :
   * 
   * <pre>one var1, ..., varn | pred1 and pred2</pre>
   * 
   * @return the expression, or null if something is null that should not be
   */
  public Expr visitExists1Pred(Exists1Pred exists1Pred)
  {
    ExprVar firstVar = (ExprVar) visit(exists1Pred.getZSchText().getZDeclList());
    ExprVar[] rest = vars_;

    Expr pred;

    Expr pred1 = visit(exists1Pred.getZSchText().getPred());
    Expr pred2 = visit(exists1Pred.getPred());

    if (pred2 == null) {
      System.err.println("pred of ExistsPred must not be null");
      return null;
    }

    if (pred1 == null) {
      pred = pred2;
    }
    else {
      pred = pred1.and(pred2);
    }

    return pred.forOne(firstVar, rest);
  }

  /**
   * uses visit to recursively translate variables and predicates.
   * <pre>\exists var1, ..., varn @ pred1 | pred2</pre> translates to
   * 
   * <pre>some var1, ... var2 | pred1 and pred2</pre>
   * @return the epxression, or null if something is null that should not be
   */
  public Expr visitExistsPred(ExistsPred existsPred)
  {
    ExprVar firstVar = (ExprVar) visit(existsPred.getZSchText().getZDeclList());
    ExprVar[] rest = vars_;

    Expr pred;

    Expr pred1 = visit(existsPred.getZSchText().getPred());
    Expr pred2 = visit(existsPred.getPred());

    if (pred2 == null) {
      System.err.println("pred of ExistsPred must not be null");
      return null;
    }

    if (pred1 == null) {
      pred = pred2;
    }
    else {
      pred = pred1.and(pred2);
    }

    if (firstVar == null) {
      System.err.println("firstVar of ExistsPred must not be null");
      return null;
    }

    return pred.forSome(firstVar, rest);
  }

  /**
   * uses visit to recurisvely translate variables and predicates
   * 
   * <pre>\forall var1, ..., varn @ pred1 | pred2</pre> translates to:
   * 
   * <pre>all var1, ..., var2 | pred1 => pred2</pre>
   */

  public Expr visitForallPred(ForallPred allPred)
  {
    ExprVar firstVar = (ExprVar) visit(allPred.getZSchText().getZDeclList());
    ExprVar[] rest = vars_;

    Expr pred;

    Expr pred1 = visit(allPred.getZSchText().getPred());
    Expr pred2 = visit(allPred.getPred());

    if (pred2 == null) {
      System.err.println("pred of allpred must not be null");
      return null;
    }

    if (pred1 == null) {
      pred = pred2;
    }
    else {
      pred = pred1.implies(pred2);
    }
    if (firstVar == null) {
      System.err.println("fistVar of allpred must not be null");
    }

    return pred.forAll(firstVar, rest);
  }

  public Expr visitFreePara(FreePara para)
  {
    return visit(para.getFreetypeList());
  }

  /***
   * creates a new abstract parent signiture, and children with multiplicity one
   * <br>
   * eg
   * <pre>A ::= B | C | D</pre>
   * 
   * translates to:
   * 
   * <pre>abstract A {}
   * one B extends A {}
   * one C extends A {}
   * one D extends A {}</pre>
   * 
   * @return null
   */

  public Expr visitFreetype(Freetype freetype)
  {
    try {
      PrimSig parent = new PrimSig(null, null, print(freetype.getName()), true, false, false, false, false);
      addSig(parent);
      Iterator<Branch> i = assertZBranchList(freetype.getBranchList()).iterator();
      while (i.hasNext()) {
        Branch branch = (Branch) i.next();
        if (branch.getExpr() != null)
          System.err.println("free types must be simple enumerations, but "
              +branch.getName()+" branch has expression "
              +branch.getExpr());
        PrimSig child = new PrimSig(null, parent, print(branch.getName()), false, false, true, false, true);
        addSig(child);
      }
      return null;
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * translates into a sig for each name, with the given name
   * <br>
   * eg <pre>[A, B, C]</pre> translates to:
   * 
   * <pre> sig A {}
   * sig B {}
   * sig C {}</pre>
   */

  public Expr visitGivenPara(GivenPara para)
  {
    for (Name name : para.getNames()) {
      try {
        addSig(new PrimSig(null, print(name)));
      }
      catch (Err e) {
        throw new RuntimeException(e);
      }
    }
    return null;
  }
  /**
   * if a sig with the name of the givenType has been encountered before, returns the sig.
   * <br>otherwise:
   * <pre>
   *           arithmos         => Int
   *           seq              => seq</pre>
   * 
   * @return the sig, or null if no sig matches
   */
  public Expr visitGivenType(GivenType givenType)
  {
    if (print(givenType.getName()).equals(ZString.ARITHMOS)) {
      return SIGINT;
    }
    if (print(givenType.getName()).equals("seq")) {
      return SEQIDX;
    }
    return sigmap_.get(print(givenType.getName()));
  }

  /**
   * translates an iff expression (schema equivalance) into an alloy iff expression. The schemas are translated into a call to the
   * predicate translated by the schema
   * 
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \iff B => pred_A[a] <=> pred_B[b]
   * </pre>
   * Currently the actual variables from the signiture are not used in the pred calls. Instead new ones are created. This works, assuming
   * the variables are declared with the same name as in the predicate declaration.
   * @return the expression
   */

  public Expr visitIffExpr(IffExpr iffExpr)
  {
    Expr[] comps = schExpr2SigComponent(iffExpr);
    return comps[0].iff(comps[1]);
  }

  /**
   * translates an implies expression (schema implication) into an alloy implies expression. The schemas are translated into a call to the
   * predicate translated by the schema
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \implies B => pred_A[a] => pred_B[b]
   *  </pre>
   * Currently the actual variables from the signiture are not used in the pred calls. Instead new ones are created. This works, assuming
   * the variables are declared with the same name as in the predicate declaration.
   * @return the expression
   */

  public Expr visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    Expr[] comps = schExpr2SigComponent(impliesExpr);
    return comps[0].implies(comps[1]);
  }

  /**
   * translates an implies predicate into an alloy implies expression.
   * <br>
   * left and right expressions are recurisvely translated using visit
   * 
   * @return the expression if it successfully translated, or null it something fails
   */
  public Expr visitImpliesPred(ImpliesPred impl)
  {
    Expr left = visit(impl.getLeftPred());
    Expr right = visit(impl.getRightPred());
    if (left == null || right == null) {
      System.err.println("Left and right of impliespred must be non null");
      return null;
    }
    return left.implies(right);
  }

  /** Ignore Latex markup paragraphs. */
  public Expr visitLatexMarkupPara(LatexMarkupPara para)
  {
    return null;
  }


  /**
   * kinds of MemPred currently translated:
   * <pre>
   * equality                   left = right
   * notin                      ! left in right
   * subseteq                   left in right
   * subset                     left in right and (not left = right)
   * less                       left < right
   * leq                        left <= right
   * greater                    left > right
   * geq                        left >= right
   * </pre>
   * otherwise assumes it is membership => left in right
   */
  public Expr visitMemPred(MemPred memPred)
  {
    if (memPred.getRightExpr() instanceof SetExpr &&
        ((SetExpr) memPred.getRightExpr()).getZExprList().size() == 1) {
      // equality
      Expr left = visit(memPred.getLeftExpr());
      Expr right = visit(memPred.getRightExpr());
      if (left == null || right == null) {
        System.err.println("Left and right of memPred must be non null");
        return null;
      }
      return left.equal(right);
    }
    if (memPred.getLeftExpr() instanceof TupleExpr &&
        memPred.getRightExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) memPred.getRightExpr();
      ZExprList exprs = ((TupleExpr) memPred.getLeftExpr()).getZExprList();
      Expr left = visit(exprs.get(0));
      Expr right = visit(exprs.get(1));
      if (left == null || right == null) {
        System.err.println("Left and right of refExpr must be non null");
        return null;
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
    }
    Expr left = visit(memPred.getLeftExpr());
    Expr right = visit(memPred.getRightExpr());
    if (left == null || right == null) {
      System.err.println("Left and right Expr of MemPred not be null");
      return null;
    }
    return left.in(right);
  }

  /** Ignore narrative paragraphs. */
  public Expr visitNarrPara(NarrPara para)
  {
    return null;
  }

  /**
   * @return an alloy integer expression with the given value
   */
  public Expr visitNumExpr(NumExpr numexpr)
  {
    return ExprConstant.makeNUMBER(numexpr.getValue().intValue());
  }

  /**
   * translates an or expression (schema disjunction) into an alloy or expression. The schemas are translated into a call to the
   * predicate translated by the schema
   * <br>
   * eg
   * <pre>
   *    A has a predicate of pred_A[a]{...}
   *    B has a predicate of pred_B[b]{...}
   *    
   *    A \lor B => pred_A[a] or pred_B[b]
   * </pre>
   * Currently the actual variables from the signiture are not used in the pred calls. Instead new ones are created. This works, assuming
   * the variables are declared with the same name as in the predicate declaration.
   * @return the expression
   */
  public Expr visitOrExpr(OrExpr orExpr)
  {
    Expr[] comps = schExpr2SigComponent(orExpr);
    return comps[0].or(comps[1]);
  }

  /**
   * translates an or predicate (ie disjunction) into an alloy or expression.
   * <br/>
   * left and right expressions are recurisvely translated using visit
   * @return the expression if it successfully translated, or null it something fails
   */
  public Expr visitOrPred(OrPred orPred)
  {
    Expr left = visit(orPred.getLeftPred());
    if (left != null) {
      return left.or(visit(orPred.getRightPred()));
    }
    System.err.println("left pred of orPred must not be null");
    return null;
  }

  /**
   * recursively calls visit on the sub expression and creates an alloy set of the translation
   * @return the expression or null if the sub expression translates to null
   */
  public Expr visitPowerExpr(PowerExpr powerExpr)
  {
    Expr body = visit(powerExpr.getExpr());
    if (body == null) {
      System.err.println("body of power expr must not be null");
      return null;
    }
    return body.setOf();
  }
  /**
   * if the type of the subexpression is not null, creates the set of the translation
   * @return the expression, or null if the subexpression translates to null
   */
  public Expr visitPowerType(PowerType powerType)
  {
    Expr body = visit(powerType.getType());
    if (body == null) {
      System.err.println("body of power type must not be null");
      return null;
    }
    return body.setOf();
  }

  /**
   * translates from a z prod expr to an alloy version using visit to recursively translate the sub expressions
   * <br/>
   * eg
   * <pre>expr1 \cross ... \cross exprn => expr1 -> ... -> exprn</pre>
   * 
   * @return the expression or null if any of the sub expressions translate to null
   */
  public Expr visitProdExpr(ProdExpr prodExpr)
  {
    Expr expr = visit(prodExpr.getZExprList().get(0));
    for (int i = 1; i < prodExpr.getZExprList().size(); i++) {
      Expr current = visit(prodExpr.getZExprList().get(i));
      if (current == null || expr == null) {
        System.err.println("body of prodexprs must not be  null");
        return null;
      }
      expr = expr.product(current);
    }
    return expr;
  }

  /**
   * translates from a prodType to the equivalant expression in alloy
   * 
   * @return the expression or null if some of the sub expressions translate to null
   */
  public Expr visitProdType(ProdType prodType)
  {
    Expr prod = null;
    for (Type2 type : prodType.getType()) {
      Expr cont = visit(type);
      if (cont == null) {
        System.err.println("elements of ProdType must not be null");
        return null;
      }
      else if (cont instanceof ExprUnary && ((ExprUnary) cont).op == ExprUnary.Op.SETOF) {
        cont = ((ExprUnary) cont).sub;
      }
      if (prod == null) {
        prod = cont;
      }
      else {
        prod = prod.product(cont);
      }
    }
    return prod;
  }

  /**
   * kinds of RefExpr translated:
   * <br>
   * subexprs are translated recursively using visit
   * <pre>
   * pfun               expr0 -> lone expr1
   * seq                seq expr0
   * arithmos           Int
   * nat                nat[] 
   * </pre>
   * otherwise if the name has is that of an already encountered signiture, it uses that signiture
   * <br>
   * finally it creates an ExprVar with the given name and a type from the type annotations.
   */
  public Expr visitRefExpr(RefExpr refExpr)
  {
    if (isInfixOperator(refExpr.getZName(), ZString.PFUN)) {
      return visit(refExpr.getZExprList().get(0)).any_arrow_lone(visit(refExpr.getZExprList().get(1)));
    }
    else if (isPostfixOperator(refExpr.getZName(), "seq")) {
      return SEQIDX.isSeq_arrow_lone(visit(refExpr.getZExprList().get(0)));
    }
    else if (print(refExpr.getZName()).equals(ZString.ARITHMOS)) {
      return SIGINT;
    }
    else if (print(refExpr.getZName()).equals(ZString.NAT)) {
      ExprVar i = ExprVar.make(null, "i", SIGINT);
      Expr sub = i.gte(ExprConstant.ZERO);
      return sub.comprehensionOver(i);
    }
    else if (print(refExpr.getZName()).equals(ZString.EMPTYSET)) {
      return NONE;
    }
    else if (sigmap_.containsKey(print(refExpr.getName()))){
      return sigmap_.get(print(refExpr.getName()));
    }
    else if (print(refExpr.getName()).contains("Delta") && sigmap_.containsKey(print(refExpr.getName()).replaceFirst("Delta", ""))) {
      return addDelta(sigmap_.get(print(refExpr.getName()).replaceFirst("Delta", "")));
    }
    else if (print(refExpr.getName()).contains("Xi")) {
      return addXi(sigmap_.get(print(refExpr.getName()).replaceFirst("Xi", "")));
    }
    else if (fields_.containsKey(print(refExpr.getName()))) {
      return ExprVar.make(null, print(refExpr.getName()), fields_.get(print(refExpr.getName())));
    }

    String name = print(refExpr.getZName());
    Expr type = visit(refExpr.getAnn(TypeAnn.class));
    if (type == null) {
      return ExprVar.make(null, name);
    }
    return ExprVar.make(null, name, type);
  }

  /** Ignore rules. */
  public Expr visitRule(Rule r)
  {
    return null;
  }

  public Expr visitSchemaType(SchemaType schemaType)
  {
    // this doesn't really work. It matches the 'first' sig which has the same number of fields, with the same names
    // could check the types
    // If there are two schemas with the same number and names of fields it fails.
    Map<String, Expr> fields = new HashMap<String, Expr>();
    for (NameTypePair p : schemaType.getSignature().getNameTypePair()) {
      fields.put(print(p.getName()), visit(p.getType()));
    }
    
    for (Sig sig : sigmap_.values()) {
      boolean equal = sig.getFields().size() == fields.size();
      for (Sig.Field field : sig.getFields()) {
        if (!fields.containsKey(field.label)) {
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
   * creates a new signiture to represent the schema
   * <br>
   * includes all the fields of the schema
   * <br>
   * if the schema contains an InclDecl, it includes all the fields of this schema
   * <br>
   * the predicate for this schema is included in the new signiture
   * <br>
   * eg
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
   * <pre>sig B {a : univ, c : C} {pred_B[a,c]} pred pred_B {... and pred_A[a]}</pre>
   * 
   */
  public Expr visitSchExpr(SchExpr schExpr)
  {
    try {
      String schName = schemaName_.get(schExpr);
      if (schName == null) {
        System.err.println("SchExprs must have names");
        return null;
      }
      Sig sig = new PrimSig(null, schName);
      Expr fieldPred = null;
      for (Decl d : schExpr.getZSchText().getZDeclList()) {
        if (d instanceof VarDecl) {
          VarDecl vardecl = (VarDecl) d;
          ZNameList nameList = vardecl.getName();
          for (Name name : nameList) {
            sig.addField(null, print(name), visit(vardecl.getExpr()));
          }
        }
        else if (d instanceof InclDecl) {
          InclDecl incdecl = (InclDecl) d;
          Expr sigfieldpred = processSigField((Sig) visit(incdecl.getExpr()), sig);
          if (fieldPred != null) {
            fieldPred = fieldPred.and(sigfieldpred);
          }
          else {
            fieldPred = sigfieldpred;
          }
        }
        else {
          System.err.println(d.getClass() + " not yet implemented");
          return null;
        }
      }
      addSig(sig);
      Expr pred =  visit(schExpr.getZSchText().getPred());
      if (fieldPred != null) {
        addSigPred(sig, fieldPred);
      }

      if (pred != null) {
        addSigPred(sig, pred);
      }
      return null;
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * <pre>{expr1, ..., exprn @ pred}</pre>
   * 
   * translates to
   * 
   * <pre>{expr1, ..., exprn | pred}</pre>
   * 
   * using visit to recursively translate the exprs and pred
   * 
   * @return the expression
   * 
   */

  public Expr visitSetCompExpr(SetCompExpr setCompExpr)
  {
    ExprVar firstVar = (ExprVar)
    visit(setCompExpr.getZSchText().getZDeclList());
    ExprVar[] rest = vars_;
    Expr pred = visit(setCompExpr.getZSchText().getPred());
    return pred.comprehensionOver(firstVar, rest);
  }

  /**
   * if the set is null or empty translates it to none
   * <br/>
   * if the set has one member, transates it to that member
   * <br/>
   * otherwise translates the set into th union of all its members
   * <br/>
   * eg
   * <pre>
   * {a, b, c} => a + b + c
   * {a} => a
   * {} => none
   * </pre>
   */
  public Expr visitSetExpr(SetExpr setExpr)
  {
    if (setExpr.getExprList() == null) {
      return NONE;
    }
    ZExprList exprs = setExpr.getZExprList();
    if (exprs.size() == 0) {
      return NONE;
    }
    else if (exprs.size() == 1) {
      return visit(exprs.get(0));
    }
    else {
      Expr expr = null;
      for (net.sourceforge.czt.z.ast.Expr e : exprs) {
        Expr ve = visit(e);
        if (ve == null) {
          System.err.println("Elements of setexpr must not be null");
          return null;
        }
        if (expr == null) {
          expr = ve;
        }
        else {
          expr = expr.plus(ve);
        }
      }
      return expr;
    }
  }
  /**
   * TODO Clare no idea what this is for, or how it works right now
   */
  public Expr visitTupleExpr(TupleExpr tupleExpr)
  {
    for (net.sourceforge.czt.z.ast.Expr e : tupleExpr.getZExprList()) {
      debug(e);
      visit(e);
      System.out.println(e.getClass());
    }
    return null;
  }

  public Expr visitTypeAnn(TypeAnn typeAnn)
  {
    return visit(typeAnn.getType());
  }

  /**
   * TODO Clare write something for this
   */
  public Expr visitVarDecl(VarDecl vDecl)
  {
    return ExprVar.make(null, print(vDecl.getName()), visit(vDecl.getExpr()));
  }


  /**
   * uses visit to recursively translate the elements fo the ZDeclList
   * <br/>
   * sets internally a list containing translations all elements other than the first, in order
   * @return the first element
   */
  public Expr visitZDeclList(ZDeclList zDeclList)
  {
    Iterator<Decl> iter = zDeclList.iterator();
    Expr result = visit(iter.next());
    if (iter.hasNext()) {
      List<ExprVar> list = new ArrayList<ExprVar>();
      while (iter.hasNext()) {
        list.add((ExprVar) visit(iter.next()));
      }
      vars_ = list.toArray(new ExprVar[0]);
    }
    else {
      vars_ = new ExprVar[0];
    }
    return result;
  }

  /**
   * visits each element of the list
   * @return null
   */
  public Expr visitZFreetypeList(ZFreetypeList list)
  {
    for (Freetype freetype : list)
    {
      visit(freetype);
    }
    return null;
  }

  public Expr visitZSect(ZSect zSect)
  {
    Source specSource = new StringSource("\\begin{zsection} "
        + "\\SECTION " + section_ + " "
        + "\\parents "
        + zSect.getName() + ", "
        + "expansion\\_rules, "
        + "simplification\\_rules"
        + "\\end{zsection}",
        section_);
    specSource.setMarkup(Markup.LATEX);
    manager_.put(new Key<Source>(section_ ,Source.class), specSource);

    for (Para para : zSect.getZParaList()) {
      visit(para);
    }

    return null;
  }

  private Expr[] schExpr2SigComponent (SchExpr2 schExpr2){
    Expr left = visit(schExpr2.getLeftExpr());
    Expr right = visit(schExpr2.getRightExpr());
    if (left instanceof PrimSig) {
      PrimSig leftsig = (PrimSig) left;
      Func leftPred = sigpreds_.get(left);
      List<Expr> content = new ArrayList<Expr>();
      for (Sig.Field f : leftsig.getFields()) {
        Expr fieldExpr= getFieldExpr(f);
        fieldExpr = ExprVar.make(null, f.label, fieldExpr);
        if (fieldExpr == null) {
          System.err.println("fieldexpr must not be null");
          return null;
        }
        content.add(fieldExpr);
      }
      Expr[] args = content.toArray(new Expr[0]);
      left = leftPred.call(args);
    }
    if (right instanceof PrimSig) {
      PrimSig rightsig = (PrimSig) right;
      Func rightPred = sigpreds_.get(right);
      List<Expr> content = new ArrayList<Expr>();
      for (Sig.Field f : rightsig.getFields()) {
        Expr fieldExpr= getFieldExpr(f);
        fieldExpr = ExprVar.make(null, f.label, fieldExpr);
        if (fieldExpr == null) {
          System.err.println("fieldexpr must not be null");
          return null;
        }
        content.add(fieldExpr);
      }
      Expr[] args = content.toArray(new Expr[0]);
      right = rightPred.call(args);
    }
    if (left == null || right == null) {
      System.err.println("left and right of SchExpr2 must not be null");
      return null;
    }
    return new Expr[] {left, right};
  }

  private Expr processSigField(Sig sigField, Sig sig) {
    // so we can easily see if a field is already present
    Map<String, Sig.Field> sigfieldnames = new HashMap<String, Sig.Field>();
    List<Expr> args = new ArrayList<Expr>();
    for (Sig.Field sigfield : sig.getFields()) {
      sigfieldnames.put(sigfield.label, sigfield);
    }

    for (Sig.Field subfield : sigField.getFields()) {
      if (!sigfieldnames.containsKey(subfield.label)){
        try {
          Sig.Field newfield = sig.addField(null, subfield.label, getFieldExpr(subfield));
          sigfieldnames.put(newfield.label, newfield);
        }
        catch (Err e) {
          throw new RuntimeException();
        }
      }
      Sig.Field field = sigfieldnames.get(subfield.label);
      args.add(ExprVar.make(null, field.label, getFieldExpr(field)));
    }
    return sigpreds_.get(sigField).call(args.toArray(new Expr[0]));
  }

  private void addSigPred (Sig sig, Expr pred) {
    Func existingPred = sigpreds_.get(sig);
    if (existingPred == null) {
      System.err.println("No pred for " + sig + " so " + pred + " cannot be added");
      return;
    }
    try {
      if (existingPred.getBody() == ExprConstant.TRUE) {
        existingPred.setBody(pred);
      }
      else {
        existingPred.setBody(existingPred.getBody().and(pred));
      }
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  private boolean isPostfixOperator(ZName name, String op)
  {
    try {
      OperatorName opName = new OperatorName(name);
      String[] opWords = opName.getWords();
      return opWords.length > 0 && op.equals(opWords[0]);
    }
    catch (OperatorName.OperatorNameException e) {
      return false;
    }
  }

  private String isInfixOperator(ZName name)
  {
    try {
      OperatorName opName = new OperatorName(name);
      if (! opName.isInfix()) return null;
      return opName.getWords()[1];
    }
    catch (OperatorName.OperatorNameException e) {
      return null;
    }
  }

  private boolean isInfixOperator(ZName name, String op)
  {
    try {
      OperatorName opName = new OperatorName(name);
      String[] opWords = opName.getWords();
      return opWords.length > 0 && op.equals(opWords[1]);
    }
    catch (OperatorName.OperatorNameException e) {
      return false;
    }
  }

  private String print(Term t)
  {
    if (t != null) return t.accept(printVisitor_);
    else return "";
  }

  private Expr visit(Term t)
  {
    if (t != null) return t.accept(this);
    return null;
  }

  private Term preprocess(Term term)
  {
    try {
      RuleTable rules = 
        manager_.get(new Key<RuleTable>(section_, RuleTable.class));
      RewriteVisitor rewriter =
        new RewriteVisitor(rules, manager_, section_);
      return Strategies.innermost(term, rewriter);
    }
    catch(Exception e) {
      throw new RuntimeException(e);
    }
  }

  private Expr processSchExpr2 (SchExpr2 schExpr2) {
    String schName = schemaName_.get(schExpr2);
    if (schName == null) {
      System.err.println("SchExpr2s must have names");
      return null;
    }
    try {
      Sig sig = new PrimSig(null, schName);
      Map<String, Expr> fields = new HashMap<String, Expr>();
      Queue<SchExpr2> subexprs = new LinkedList<SchExpr2>();
      subexprs.offer((SchExpr2) schExpr2);

      while (!subexprs.isEmpty()) {
        SchExpr2 subexpr = subexprs.poll();
        if (subexpr.getLeftExpr() instanceof RefExpr) {
          if (!fields.containsKey(print(subexpr.getLeftExpr()))) {
            Expr field = visit(subexpr.getLeftExpr());
            fields.put(print(subexpr.getLeftExpr()), field);
          }
        }
        else if (subexpr.getLeftExpr() instanceof SchExpr2) {
          subexprs.offer((SchExpr2) subexpr.getLeftExpr());
        }
        if (subexpr.getRightExpr() instanceof RefExpr) {
          if (!fields.containsKey(print(subexpr.getRightExpr()))) {
            Expr field = visit(subexpr.getRightExpr());
            fields.put(print(subexpr.getRightExpr()),field);
          }
        }
        else if (subexpr.getRightExpr() instanceof SchExpr2) {
          subexprs.offer((SchExpr2) subexpr.getRightExpr());
        }
      }
      for (Entry<String, Expr> entry : fields.entrySet()) {
        processSigField((Sig) entry.getValue(), sig);
      }
      addSig(sig);
      addSigPred(sig, visit(schExpr2));
      return null;
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  private void addSig (Sig sig) {
    sigmap_.put(sig.label, sig);
    sigOrder_.add(sig);
    List<ExprVar> vars = new ArrayList<ExprVar>();
    for (Sig.Field f : sig.getFields()) {
      vars.add(ExprVar.make(null, f.label, getFieldExpr(f)));
      fields_.put(f.label, getFieldExpr(f));
    }
    try {
      Func f = new Func(null, "pred_" + sig.label, vars , null);
      f.setBody(ExprConstant.TRUE);
      sigpreds_.put(sig, f);
      Expr[] fields = new Expr[sig.getFields().size()];
      for (int i = 0; i < sig.getFields().size(); i++) fields[i] = sig.getFields().get(i);
      sigfacts_.put(sig, f.call(fields));
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  private Sig addDelta(Sig sig) {
    try {
      PrimSig delta = new PrimSig(null, "Delta" + sig.label);
      for (Sig.Field field : sig.getFields()) {
        delta.addField(null, field.label, getFieldExpr(field));
        delta.addField(null, field.label + "'", getFieldExpr(field));
      }
      addSig(delta);
      return delta;
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  private Expr addXi(Sig sig) {
    try {
      PrimSig xi = new PrimSig(null, "Xi" + sig.label);
      for (Sig.Field field : sig.getFields()) {
        xi.addField(null, field.label, getFieldExpr(field));
        xi.addField(null, field.label + "'", getFieldExpr(field));
      }
      addSig(xi);
      for (int i = 0; i < xi.getFields().size() ; i += 2) {
        addSigPred(xi, xi.getFields().get(i).equal(xi.getFields().get(i + 1)));
      }
      return xi;
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  private Expr build(Expr expr, Map<String, Expr> vars) {
    if (expr instanceof ExprCall) {
      expr = (sigmap_.get(((ExprCall) expr).fun.label.replaceFirst("pred_", "")));      
    }
    if (expr instanceof Sig) {
      Sig signiture = (Sig) expr;
      Expr[] exprs = new Expr[signiture.getFields().size()];
      for (int i = 0; i < signiture.getFields().size(); i++) {
        exprs[i] = vars.get(signiture.getFields().get(i).label);
      }
      return sigpreds_.get(signiture).call(exprs);
    }
    else if (expr instanceof ExprList) {
      ExprList exprList = (ExprList) expr;
      Expr ret = null;
      for (Expr e : exprList.args) {
        e = build(e, vars);
        if (ret == null) {
          ret = e;
        }
        else {
          if (exprList.op == ExprList.Op.AND) {
            ret = ret.and(e);
          }
          else if (exprList.op == ExprList.Op.OR) {
            ret = ret.or(e);
          }
        }
      }
      return ret;
    }
    System.err.println("Not fully translated: " + expr.getClass() + " " + expr);
    return null;
  }

  public static Expr getFieldExpr (Sig.Field field)
  {
    // this has the form (all this | this . (A <: label) in def)
    // getting it out is yucky - not sure how to get the end bit neatly
    // also not sure if it ever has a different structure

    return ((ExprBinary) ((ExprQuant) field.boundingFormula).sub).right;
  }

  private void debug(Term t)
  {
    StringWriter foo = new StringWriter();
    PrintUtils.print(t, foo, manager_, section_, Markup.UNICODE);
    System.out.println("Debug: " + foo);
  }

  class AlloyPrintVisitor extends PrintVisitor
  implements DecorExprVisitor<String>,
  RefExprVisitor<String>
  {
    public String visitZName(ZName zName)
    {
      String word = zName.getWord();
      word = word.replaceAll(ZString.DELTA, "Delta");
      word = word.replaceAll(ZString.XI, "Xi");
      word = word.replaceAll("\u03A6", "Psi");
      word = word.replaceAll("\u2295", "Distro");
      word = word.replaceAll("/", "Slash");

      if (names_.containsKey(zName.getId())) {
        return names_.get(zName.getId());
      }
      return word + visit(zName.getStrokeList());
    }


    public String visitInStroke(InStroke inStroke)
    {
      return "_in";
    }

    public String visitNextStroke(NextStroke nextStroke)
    {
      return "'";
    }

    public String visitOutStroke(OutStroke outStroke)
    {
      return "_out";
    }



    public String visitDecorExpr(DecorExpr decorExpr)
    {
      return decorExpr.getExpr().accept(this) +
      decorExpr.getStroke().accept(this);
    }

    public String visitRefExpr(RefExpr refExpr)
    {
      return refExpr.getName().accept(this);
    }
  }

}
