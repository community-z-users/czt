/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval;

import java.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z.util.ZString;

import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** Flattens a Pred/Expr term into a list of FlatPred objects.
 *  The visit* methods add subclasses of FlatPred into the list flat_.
 *  Each visit*Expr method returns a RefName, which is the result of
 *  the expression.  Each visit*Pred method returns null.
 */
public class Flatten
    implements
      TermVisitor,
      AndPredVisitor,
      OrPredVisitor,
      ImpliesPredVisitor,
      IffPredVisitor,
      NegPredVisitor,
      MemPredVisitor,
      FalsePredVisitor,
      TruePredVisitor,
      ExistsPredVisitor,
      ForallPredVisitor,

      NameVisitor,
      NumExprVisitor,
      ApplExprVisitor,
      RefExprVisitor,
      PowerExprVisitor,
      SetExprVisitor,
      SetCompExprVisitor,
      ProdExprVisitor,
      TupleExprVisitor
{
  private List flat_;

  private static long newNameNum = 0;

  // TODO: allow this to be customised.
  private Factory factory_ = new Factory();
  private static final List empty = new ArrayList();

  protected RefName createNewName()
  {
    return factory_.createRefName("tmp"+(newNameNum++), empty, null);
  }

  /** Throws a 'not yet implemented' exception. */
  protected Term notYet(Term t) {
    throw new RuntimeException("Flatten does not yet handle: " + t);
  }

  public Flatten()
  {
    VisitorUtils.checkVisitorRules(this);
  }

  /** Flattens the toFlatten AST into a list of FlatPred predicates. */
  public void flattenPred(Pred toFlatten, List destination)
  {
    flat_ = destination;
    toFlatten.accept(this);
  }

  /** Flattens the toFlatten AST into a list of FlatPred predicates. */
  public RefName flattenExpr(Expr toFlatten, List destination)
  {
    flat_ = destination;
    return (RefName)toFlatten.accept(this);
  }  
  
  /** We throw an error if we reach a kind of term that we do not handle. */
  public Object visitTerm(Term term) {
    return notYet(term);
  }

  /** Adds both conjuncts to the flatten list. */
  public Object visitAndPred(AndPred p) {
    ((Pred)p.getLeftPred()).accept(this);
    ((Pred)p.getRightPred()).accept(this);
    return null;
  }

  /////////////// TODO: implement these, or unfold them //////////////////
  public Object visitOrPred(OrPred p) { return notYet(p); }
  public Object visitImpliesPred(ImpliesPred p) { return notYet(p); }
  public Object visitIffPred(IffPred p) { return notYet(p); }
  public Object visitNegPred(NegPred p) { return notYet(p); }

  public Object visitMemPred(MemPred p) {
    Expr lhs = p.getLeftExpr();
    Expr rhs = p.getRightExpr();
    if (rhs instanceof SetExpr
	&& ((SetExpr)rhs).getExpr().size() == 1) {
      // We have an equality
      rhs = (Expr)((SetExpr)rhs).getExpr().get(0);
      flat_.add(new FlatEquals((RefName)lhs.accept(this),(RefName)rhs.accept(this)));
      return null;
    } 
    /* else if (rhs instanceof RefExpr
	       && lhs instanceof TupleExpr
	       && ((TupleExpr)lhs).getExpr().size() == 2
	       && isKnownRelation((RefExpr)rhs))
    */
    flat_.add(new FlatMember((RefName)rhs.accept(this), 
			     (RefName)lhs.accept(this)));
    return null;
  }


  /////////////// TODO: clear the list? insert FalseFalse? ///////////////
  public Object visitFalsePred(FalsePred p) {
    return notYet(p);
  }

  public Object visitTruePred(TruePred p) {
    // Ignore it.
    return null;
  }

  /////////////// TODO: implement these, or unfold them //////////////////
  public Object visitExistsPred(ExistsPred p) {
    return notYet(p);
  }

  public Object visitForallPred(ForallPred p) {
    return notYet(p);
  }

  /** Name objects are returned unchanged. */
  public Object visitName(Name e)
  { return e; }

  /** Simple RefExpr objects are returned unchanged. */
  public Object visitRefExpr(RefExpr e) {
    if (e.getExpr().size() != 0)
      return notYet(e);
    return e.getRefName();
  }

  /** NumExpr objects are converted into tmp = Num. */
  public Object visitNumExpr(NumExpr e)
  {     
    RefName result = createNewName();
    flat_.add(new FlatConst(result,e));
    return result;
  }

  /** Each ApplExpr is flattened into a different kind of FlatPred. */
  public Object visitApplExpr(ApplExpr e) {
    Expr func = (Expr) e.getLeftExpr();
    Expr arg = (Expr) e.getRightExpr();
    List argList = null;
    RefName result = createNewName();

    if (arg instanceof TupleExpr)
      argList = ((TupleExpr) arg).getExpr();

    if (func instanceof RefExpr
        && ((RefExpr) func).getRefName().getStroke().size() == 0) {
      String funcname = ((RefExpr) func).getRefName().getWord();
      if (funcname.equals(ZString.ARG_TOK + ZString.PLUS + ZString.ARG_TOK)) 
        flat_.add(new FlatPlus(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + ZString.MULT + ZString.ARG_TOK))
        flat_.add(new FlatMult(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
       else if (funcname.equals(ZString.ARG_TOK + "div" + ZString.ARG_TOK))
        flat_.add(new FlatDiv(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + "mod" + ZString.ARG_TOK))
        flat_.add(new FlatMod(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK))
        flat_.add(new FlatRangeSet(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals("#" + ZString.ARG_TOK)) {
        RefName argVar = (RefName) arg.accept(this);
        flat_.add(new FlatCard(argVar, result));
      }
      else if (funcname.equals(ZString.NEG + ZString.ARG_TOK)) {
        RefName argVar = (RefName) arg.accept(this);
        flat_.add(new FlatNegate(argVar, result));
      }
      
      // else if (...)   TODO: add more cases...
      else {
        return notYet(e);
        // TODO: flat_.add(new FlatAppl(func, args, result));
      }
    }
    else {
      return notYet(e);
    }
    return result;
  }

  public Object visitPowerExpr(PowerExpr e) { return notYet(e); }
  
  public Object visitSetExpr(SetExpr e) 
  {
    List elements = e.getExpr();
    List refnames = new ArrayList();
    for (Iterator i = elements.iterator(); i.hasNext(); ) {
      Expr elem = (Expr)i.next();
      refnames.add(elem.accept(this));
    }
    RefName result = createNewName();
    flat_.add(new FlatDiscreteSet(refnames, result));
    return result;
  }
  
  public Object visitSetCompExpr(SetCompExpr e) {return notYet(e); }

  public Object visitProdExpr(ProdExpr e) { return notYet(e); }
  public Object visitTupleExpr(TupleExpr e) { return notYet(e); }

/*
  public Object visitFreetype(Freetype zedObject) { return zedObject; }
  public Object visitNameNamePair(NameNamePair zedObject) {return zedObject; }
  public Object visitLetExpr(LetExpr zedObject) {return zedObject; }
  public Object visitSignature(Signature zedObject) {return zedObject; }
  public Object visitConstDecl(ConstDecl zedObject) {return zedObject; }
  public Object visitProdType(ProdType zedObject) {return zedObject; }
  public Object visitDecl(Decl zedObject) {return zedObject; }
  public Object visitImpliesExpr(ImpliesExpr zedObject) {return zedObject; }
  public Object visitMuExpr(MuExpr zedObject) {return zedObject; }
  public Object visitSchExpr2(SchExpr2 zedObject) {return zedObject; }
  public Object visitExistsExpr(ExistsExpr zedObject) {return zedObject; }
  public Object visitExists1Expr(Exists1Expr zedObject) {return zedObject; }
  public Object visitForallExpr(ForallExpr zedObject) {return zedObject; }
  public Object visitVarDecl(VarDecl zedObject) {return zedObject; }
  public Object visitCompExpr(CompExpr zedObject) {return zedObject; }
  public Object visitBindExpr(BindExpr zedObject) {return zedObject; }
  public Object visitCondExpr(CondExpr zedObject) {return zedObject; }
  public Object visitNameExprPair(NameExprPair zedObject) {return zedObject; }
  public Object visitTupleSelExpr(TupleSelExpr zedObject) {return zedObject; }
  public Object visitLambdaExpr(LambdaExpr zedObject) {return zedObject; }
  public Object visitIffExpr(IffExpr zedObject) {return zedObject; }
  public Object visitQntExpr(QntExpr zedObject) {return zedObject; }
  public Object visitNameTypePair(NameTypePair zedObject) {return zedObject; }
  public Object visitSchText(SchText zedObject) {return zedObject; }
  public Object visitQnt1Expr(Qnt1Expr zedObject) {return zedObject; }
  public Object visitOperand(Operand zedObject) {return zedObject; }
  public Object visitProjExpr(ProjExpr zedObject) {return zedObject; }
  public Object visitBranch(Branch zedObject) {return zedObject; }
  public Object visitGenType(GenType zedObject) {return zedObject; }
  public Object visitPreExpr(PreExpr zedObject) {return zedObject; }
  public Object visitExprPred(ExprPred zedObject) {return zedObject; }
  public Object visitGivenType(GivenType zedObject) {return zedObject; }
  public Object visitInclDecl(InclDecl zedObject) {return zedObject; }
  public Object visitPred(Pred zedObject) {return zedObject; }
  public Object visitSchemaType(SchemaType zedObject) {return zedObject; }
  public Object visitBindSelExpr(BindSelExpr zedObject) {return zedObject; }
  public Object visitDeclName(DeclName zedObject) {return zedObject; }
  public Object visitOrExpr(OrExpr zedObject) {return zedObject; }
  public Object visitSpec(Spec zedObject) {return zedObject; }
  public Object visitHideExpr(HideExpr zedObject) {return zedObject; }
  public Object visitPowerType(PowerType zedObject) {return zedObject; }
  public Object visitAndExpr(AndExpr zedObject) {return zedObject; }
  public Object visitRenameExpr(RenameExpr zedObject) {return zedObject; }
  public Object visitThetaExpr(ThetaExpr zedObject) {return zedObject; }
  public Object visitPipeExpr(PipeExpr zedObject) {return zedObject; }
  public Object visitNegExpr(NegExpr zedObject) {return zedObject; }
  public Object visitDecorExpr(DecorExpr zedObject) {return zedObject; }
  public Object visitExists1Pred(Exists1Pred zedObject) {return zedObject; }
  public Object visitSchExpr(SchExpr zedObject) {return zedObject; }
*/
}

