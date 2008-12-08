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
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.ExprPred;
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
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
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
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.TruePred;
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
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.Exists1PredVisitor;
import net.sourceforge.czt.z.visitor.ExistsPredVisitor;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.ForallPredVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.IffExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
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
import net.sourceforge.czt.z.visitor.SetCompExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;
import net.sourceforge.czt.z.visitor.TypeAnnVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.visitor.ZSchTextVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.visitor.RuleVisitor;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQuant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;


public class Z2Alloy
implements TermVisitor<Expr>,
AndExprVisitor<Expr>,
AndPredVisitor<Expr>,
ApplExprVisitor<Expr>,
AxParaVisitor<Expr>,
ConjParaVisitor<Expr>,
//ConstDeclVisitor<Expr>,
DecorExprVisitor<Expr>,
Exists1PredVisitor<Expr>,
ExistsPredVisitor<Expr>,
ExprPredVisitor<Expr>,
ForallPredVisitor<Expr>,
FreeParaVisitor<Expr>,
FreetypeVisitor<Expr>,
GivenParaVisitor<Expr>,
GivenTypeVisitor<Expr>,
IffExprVisitor<Expr>,
ImpliesExprVisitor<Expr>,
ImpliesPredVisitor<Expr>,
InclDeclVisitor<Expr>,
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
SchExprVisitor<Expr>,
SetCompExprVisitor<Expr>,
SetExprVisitor<Expr>,
TypeAnnVisitor<Expr>,
TruePredVisitor<Expr>,
VarDeclVisitor<Expr>,
ZDeclListVisitor<Expr>,
ZFreetypeListVisitor<Expr>,
ZSchTextVisitor<Expr>,
ZSectVisitor<Expr>
{
  private SectionManager manager_;
  private AlloyPrintVisitor printVisitor_ = new AlloyPrintVisitor();
  private String section_ = "z2alloy";
  private boolean unfolding_ = false;

  public Map<String, Sig> sigmap = new HashMap<String, Sig>();
  public Map<Sig, Func> sigpreds = new HashMap<Sig,Func>();

  /**
   * A mapping from ZName ids to alloy names.
   */
  private Map<String,String> names_ = new HashMap<String,String>();

  public Z2Alloy(SectionManager manager)
  throws Exception
  {
    manager_ = manager;
  }

  //==================== Visitor Methods ==================

  public Expr visitTerm(Term term)
  {
    System.err.println(term.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitAndExpr(AndExpr andExpr)
  {
    Expr[] comps = schExpr2SigComponent(andExpr);
    return comps[0].and(comps[1]);
  }

  public Expr visitAndPred(AndPred andPred)
  {
    Expr left = visit(andPred.getLeftPred());
    if (left != null) {
      return left.and(visit(andPred.getRightPred()));
    }
    System.err.println("left pred of andpred must not be null");
    return null;
  }

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
          List<ExprVar> vars = new ArrayList<ExprVar>();
          vars.add(ExprVar.make(null, "ex", UNIV.setOf()));
          vars.add(ExprVar.make(null, "r", UNIV.product(UNIV)));
          try {
            Func ndres = new Func(null, "ndres", vars, UNIV.product(UNIV));
            return ndres.call(left, right);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
        }
        System.err.println(applExpr.getClass() + " not yet implemented napp");
        return null;
      }
    }
    else { // application
      if (applExpr.getLeftExpr() instanceof RefExpr) {
        RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
        if (print(refExpr.getName()).equals("dom")) {
          List<ExprVar> vars = new ArrayList<ExprVar>();
          vars.add(ExprVar.make(null, "r", UNIV.product(UNIV)));
          try {
            Func dom = new Func(null, "dom", vars, UNIV.setOf());
            Expr body = visit(applExpr.getRightExpr());
            return dom.call(body);
          }
          catch (Err e) {
            throw new RuntimeException(e);
          }
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
                  cDecl.getName().accept(new PrintVisitor()));
            exprSource.setMarkup(Markup.LATEX);
            net.sourceforge.czt.z.ast.Expr toBeNormalized =
              ParseUtils.parseExpr(exprSource, section_, manager_);
            result = (net.sourceforge.czt.z.ast.Expr) preprocess(toBeNormalized);
          }
          if (result instanceof RefExpr) {
            PrimSig sig = new PrimSig(null, print(cDecl.getName()));
            addField(sig, "data", visit(cDecl.getExpr()));
            addSig(sig);
            return null;
          }
          if (result instanceof SchExpr2) {
            PrimSig sig = new PrimSig(null, print(cDecl.getName()));
            Map<String, Expr> fields = new HashMap<String, Expr>();
            Queue<SchExpr2> subexprs = new LinkedList<SchExpr2>();
            subexprs.offer((SchExpr2) result);

            while (!subexprs.isEmpty()) {
              SchExpr2 schExpr2 = subexprs.poll();
              if (schExpr2.getLeftExpr() instanceof RefExpr) {
                if (!fields.containsKey(print(schExpr2.getLeftExpr()))) {
                  Expr field = visit(schExpr2.getLeftExpr());
                  fields.put(print(schExpr2.getLeftExpr()), field);
                }
              }
              else if (schExpr2.getLeftExpr() instanceof SchExpr2) {
                subexprs.offer((SchExpr2) schExpr2.getLeftExpr());
              }
              if (schExpr2.getRightExpr() instanceof RefExpr) {
                if (!fields.containsKey(print(schExpr2.getRightExpr()))) {
                  Expr field = visit(schExpr2.getRightExpr());
                  fields.put(print(schExpr2.getRightExpr()),field);
                }
              }
              else if (schExpr2.getRightExpr() instanceof SchExpr2) {
                subexprs.offer((SchExpr2) schExpr2.getRightExpr());
              }
            }
            for (Entry<String, Expr> entry : fields.entrySet()) {
              processSigField((Sig) entry.getValue(), sig);
            }
            addSig(sig);
            addSigPred(sig, visit(result));
            return null;
          }
          PrimSig sig = new PrimSig(null, sigName);
          Expr fieldPred = null;
          for (Decl d : ((SchExpr)result).getZSchText().getZDeclList()) {
            if (d instanceof VarDecl) {
              VarDecl vardecl = (VarDecl) d;
	      ZNameList nameList = vardecl.getName();
	      for (Name name : nameList) {
		addField(sig, print(name), visit(vardecl.getExpr()));
	      }
            }
            else if (d instanceof InclDecl) {
              InclDecl incdecl = (InclDecl) d;
              net.sourceforge.czt.z.ast.Expr expr = incdecl.getExpr();
              Expr sigfieldpred = processSigField((Sig) visit(expr), sig);
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
          Expr pred =  visit(((SchExpr)result).getZSchText().getPred());
          if (fieldPred != null) {
            addSigPred(sig, fieldPred);
          }

          if (pred != null) {
            addSigPred(sig, pred);
          }
          return null;

        }
        catch (CommandException e) {
          throw new RuntimeException(e);
        }
        catch (IOException e) {
          throw new RuntimeException(e);
        }
        catch (Err e) {
          throw new RuntimeException(e);
        }
      }
    }
    System.err.println(para.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitConjPara(ConjPara cPara)
  {
    System.err.println(cPara.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitDecorExpr(DecorExpr decorExpr)
  {
    System.err.println(decorExpr.getClass() + " not yet implemented");
    return null;
  }
  
  public Expr visitExists1Pred(Exists1Pred exists1Pred)
  {
    List<ExprVar> vars = new ArrayList<ExprVar>();
    for (Decl d : exists1Pred.getZSchText().getZDeclList()) {
      Expr var = visit(d);
      if (var == null) {
        System.err.println("decl of ExistsPred must not be null");
      }
      if (!(var instanceof ExprVar)) {
        System.err.println("decl of ExistsPred must be a exprvar");
      }
      vars.add((ExprVar) var);
    }
    ExprVar firstVar = vars.get(0);
    vars.remove(0);
    
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
    
    return pred.forOne(firstVar, vars.toArray(new ExprVar[0]));
  }

  public Expr visitExistsPred(ExistsPred existsPred)
  {
    List<ExprVar> vars = new ArrayList<ExprVar>();
    for (Decl d : existsPred.getZSchText().getZDeclList()) {
      Expr var = visit(d);
      if (var == null) {
        System.err.println("decl of ExistsPred must not be null");
      }
      if (!(var instanceof ExprVar)) {
        System.err.println("decl of ExistsPred must be a exprvar");
      }
      vars.add((ExprVar) var);
    }
    ExprVar firstVar = vars.get(0);
    vars.remove(0);
    
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
    
    return pred.forSome(firstVar, vars.toArray(new ExprVar[0]));
  }

  public Expr visitExprPred(ExprPred exprPred)
  {
    System.err.println(exprPred.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitForallPred(ForallPred allPred)
  {
    List<ExprVar> vars = new ArrayList<ExprVar>();
    for (Decl d : allPred.getZSchText().getZDeclList()) {
      Expr var = visit(d);
      if (var == null) {
        System.err.println("decl of allpred must not be null");
      }
      if (!(var instanceof ExprVar)) {
        System.err.println("decl of allpred must be a exprvar");
      }
      vars.add((ExprVar) var);
    }
    ExprVar firstVar = vars.get(0);
    vars.remove(0);
    
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
    
    return pred.forAll(firstVar, vars.toArray(new ExprVar[0]));
  }

  public Expr visitFreePara(FreePara para)
  {
    return visit(para.getFreetypeList());
  }

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

  public Expr visitGivenType(GivenType givenType)
  {
    Expr type = sigmap.get(print(givenType.getName()));
    if (type == null){
      System.err.println(print(givenType.getName()) + "not present");
    }
    return type;
  }

  public Expr visitIffExpr(IffExpr iffExpr)
  {
    Expr[] comps = schExpr2SigComponent(iffExpr);
    return comps[0].iff(comps[1]);
  }

  public Expr visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    Expr[] comps = schExpr2SigComponent(impliesExpr);
    return comps[0].implies(comps[1]);
  }

  public Expr visitImpliesPred(ImpliesPred impl)
  {
    System.err.println(impl.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitInclDecl(InclDecl inclDecl)
  {
    System.err.println(inclDecl.getClass() + " not yet implemented");
    return null;

  }

  /** Ignore Latex markup paragraphs. */
  public Expr visitLatexMarkupPara(LatexMarkupPara para)
  {
    return null;
  }

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

  public Expr visitNumExpr(NumExpr numexpr)
  {
    System.err.println(numexpr.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitOrExpr(OrExpr orExpr)
  {
    Expr[] comps = schExpr2SigComponent(orExpr);
    return comps[0].or(comps[1]);
  }

  public Expr visitOrPred(OrPred orPred)
  {
    Expr left = visit(orPred.getLeftPred());
    if (left != null) {
      return left.or(visit(orPred.getRightPred()));
    }
    System.err.println("left pred of orPred must not be null");
    return null;
  }

  public Expr visitPowerExpr(PowerExpr powerExpr)
  {
    Expr body = visit(powerExpr.getExpr());
    if (body == null) {
      System.err.println("body of power expr must not be null");
      return null;
    }
    return body.setOf();
  }

  public Expr visitPowerType(PowerType powerType)
  {
    Expr body = visit(powerType.getType());
    if (body == null) {
      System.err.println("body of power type must not be null");
      return null;
    }
    return body.setOf();
  }

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

  public Expr visitProdType(ProdType prodType)
  {
    Expr prod = null;
    for (Type2 type : prodType.getType()) {
      Expr cont = visit(type);
      if (cont == null) {
        System.err.println("elements of ProdType must not be null");
        return null;
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

  public Expr visitRefExpr(RefExpr refExpr)
  {
    if (isInfixOperator(refExpr.getZName(), ZString.PFUN)) { // pfun
      return visit(refExpr.getZExprList().get(0)).any_arrow_lone(visit(refExpr.getZExprList().get(1)));
    }
    if (isPostfixOperator(refExpr.getZName(), "seq")) { // seq
      return SEQIDX.any_arrow_lone(visit(refExpr.getZExprList().get(0)));
    }
    if (sigmap.containsKey(print(refExpr.getName()))){
      return sigmap.get(print(refExpr.getName()));
    }
    if (print(refExpr.getName()).contains(".")){
      String name = print(refExpr.getName());
      String field = name.substring(0, name.indexOf('.'));
      String subfield = name.substring(name.indexOf('.') + 1);
      Expr fieldvar = ExprVar.make(null, field);
      Expr subfieldvar = ExprVar.make(null, subfield);
      return fieldvar.join(subfieldvar);
    }
    TypeAnn type = refExpr.getAnn(TypeAnn.class);

    return ExprVar.make(null, print(refExpr.getZName()), visit(type));
  }

  public Expr visitRule(Rule r)
  {
    System.err.println(r.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitSchExpr(SchExpr schExpr)
  {
    System.err.println(schExpr.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitSetCompExpr(SetCompExpr setCompExpr)
  {
    System.err.println(setCompExpr.getClass() + " not yet implemented");
    return null;
  }

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
      System.err.println(setExpr.getClass() + " not yet implemented");
      return null;
    }
  }

  public Expr visitTypeAnn(TypeAnn typeAnn)
  {
    return visit(typeAnn.getType());
  }

  public Expr visitTruePred(TruePred truePred)
  {
    System.err.println(truePred.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitVarDecl(VarDecl vDecl)
  {
    return ExprVar.make(null, print(vDecl.getName()), visit(vDecl.getExpr()));
  }

  public Expr visitZDeclList(ZDeclList zDeclList)
  {
    System.err.println(zDeclList.getClass() + " not yet implemented");
    return null;
  }

  public Expr visitZFreetypeList(ZFreetypeList list)
  {
    for (Freetype freetype : list)
    {
      visit(freetype);
    }
    return null;
  }

  public Expr visitZSchText(ZSchText zSchText)
  {
    System.err.println(zSchText.getClass() + " not yet implemented");
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
      Func leftPred = sigpreds.get(left);
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
      Func rightPred = sigpreds.get(right);
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

  private Sig.Field addField (Sig sig, String label, Expr bound) throws Err {
    return sig.addField(null, label, bound);
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
          Sig.Field newfield = addField(sig, subfield.label, getFieldExpr(subfield));
          sigfieldnames.put(newfield.label, newfield);
        }
        catch (Err e) {
          throw new RuntimeException();
        }
      }
      Sig.Field field = sigfieldnames.get(subfield.label);
      args.add(ExprVar.make(null, field.label, getFieldExpr(field)));
    }
    return sigpreds.get(sigField).call(args.toArray(new Expr[0]));
  }

  private void addSigPred (Sig sig, Expr pred) {
    Func existingPred = sigpreds.get(sig);
    if (existingPred == null) {
      System.err.println("No pred for " + sig + " so " + pred + " cannot be added");
      return;
    }
    try {
      if (existingPred.getBody() == ExprConstant.FALSE) {
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

  private void addSig (Sig sig) {
    sigmap.put(sig.label, sig);
    List<ExprVar> vars = new ArrayList<ExprVar>();
    for (Sig.Field f : sig.getFields()) {
      vars.add(ExprVar.make(null, f.label, getFieldExpr(f)));
    }
    Func f = null;
    try {
      f = new Func(null, "pred_" + sig.label, vars , null);
      sigpreds.put(sig, f);
    }
    catch (Err e) {
      throw new RuntimeException(e);
    }
  }

  public static Expr getFieldExpr (Sig.Field field)
  {
    // this has the form (all this | this . (A <: label) in def)
    // getting it out is yucky - not sure how to get the end bit neatly
    // also not sure if it ever has a different structure

    ExprQuant q = (ExprQuant) field.boundingFormula;
    ExprBinary bin = (ExprBinary) q.sub;
    return bin.right;
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
      word = word.replaceAll("\u03A8", "Psi");

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
