/**
Copyright 2003 Mark Utting
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
package net.sourceforge.czt.z2b;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z2b.*;


/**
 * <p>This class prints a Z predicate/expression out in B syntax.
 *
 * @author Mark Utting
 */
public class BTermWriter
  extends AstTermVisitor
  implements AndPredVisitor,
	     OrPredVisitor,
	     ImpliesPredVisitor,
	     IffPredVisitor,
	     NegPredVisitor,
	     MemPredVisitor,
	     FalsePredVisitor,
	     TruePredVisitor,

	     NameVisitor,
	     NumExprVisitor,
	     ApplExprVisitor
{
  private BWriter out = null;

  private static final Logger sLogger
    = Logger.getLogger("net.sourceforge.czt.z2b");


  /**
   * Constructor for BWriteTerm
   *
   * @param dest Where to print the B predicates.
   *
   */
  public BTermWriter(BWriter dest) {
    out = dest;
  }

  /** Print a list of predicates, separated by '&' and newlines.
   *  <esc> requires preds.size() > 0 </esc>
   */
  public void printPreds(List preds) {
    int prec = out.getPrec("&");
    out.beginPrec(prec);
    Iterator i = preds.iterator();
    assert i.hasNext();
    while (true) {
      Pred p = (Pred)i.next();
      printPred(p);
      if ( ! i.hasNext())
	break;
      out.printSeparator(" & ");
    }
    out.endPrec(prec);
  }

  /** Print a single Z predicate out in B syntax.
   *  The priority of the surrounding context of the predicate 
   *  should be set by the caller if necessary.  Usually the
   *  current context is sufficient.
   */
  public void printPred(Pred p) {
      p.accept(this);
  }

  /** Print a Z expression out in B syntax.
   *  The priority of the surrounding context of the predicate 
   *  should be set by the caller if necessary.
   */
  public void printExpr(Expr e) {
      e.accept(this);
  }



  //================== Auxiliary functions ===================

  /** This prints a comma-separated list of all the names in a SchText,
   *  and returns the associated type conditions as one predicate.
   */
  protected Pred splitSchText(SchText s) {
    Iterator i = s.getDecl().iterator();
    Pred result = null;
    while (i.hasNext()) {
      Decl d = (Decl)i.next();
      if (d instanceof VarDecl) {
	VarDecl vdecl = (VarDecl)d;
	Iterator vars = vdecl.getDeclName().iterator();
	while (vars.hasNext()) {
	  DeclName n = (DeclName)vars.next();
	  Pred ntype = Create.memPred(n,vdecl.getExpr());
	  if (result == null) {
	    result = ntype;
	  } else {
	    out.print(",");
	    result = Create.andPred(result,ntype);
	  }
	  out.printName(n);
	}
      } else if (d instanceof ConstDecl) {
	ConstDecl cdecl = (ConstDecl)d;
	DeclName n = cdecl.getDeclName();
	Pred ntype = Create.eqPred(n, cdecl.getExpr());
	if (result == null) {
	  result = ntype;
	} else {
	  out.print(",");
	  result = Create.andPred(result,ntype);
	}
	out.printName(n);
      } else {
	throw new BException("Cannot handle complex schema text: " + d);
      }
    }
    return result;
  }

  /** This handles all unary functions:   foo(Arg).
   *  @param bFunc  The B name of the function
   *  @param arg      The argument predicate/expression
   */
  protected void unaryFunc(String bFunc, Term arg) {
    out.beginPrec(out.TIGHTEST);
    out.print(bFunc);
    // beginPrec will add the opening "(".
    out.beginPrec(out.LOOSEST);
    arg.accept(this);
    // endPrec will add the closing "(".
    out.endPrec(out.LOOSEST);
    out.endPrec(out.TIGHTEST);
  }


  /** This handles all infix operators (except '.').
   *  @param bOp  The B name of the binary operator
   *  @param left   Left predicate/expression
   *  @param right  Right predicate/expression
   *  All B infix operators (except '.') are left associative.
   */
  protected void infixOp(String bOp, Term left, Term right) {
    int prec = out.getPrec(bOp);
    out.beginPrec(prec);

    left.accept(this);
    out.print(" " + bOp + " ");

    // Now process the right arg at a lower precedence.
    out.beginPrec(prec-1);
    right.accept(this);
    out.endPrec(prec-1);
      
    out.endPrec(prec);
  }


  /* =============================================
     The visitor methods.
     These all write output via the BWriter object.
     They do not change the AST they are visiting.
     =============================================
  */

  public Object visitAndPred(AndPred p) {
    infixOp("&", p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitOrPred(OrPred p) {
    infixOp("or", p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitImpliesPred(ImpliesPred p) {
    infixOp("=>", p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitIffPred(IffPred p) {
    infixOp("<=>", p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitNegPred(NegPred p) {
    unaryFunc("not", p.getPred());
    return p;
  }

  public Object visitMemPred(MemPred p) {
    infixOp(":", p.getLeftExpr(), p.getRightExpr());
    return p;
  }

  public Object visitFalsePred(FalsePred p) {
    out.print("false");
    return p;
  }

  public Object visitTruePred(TruePred p) {
    out.print("true");
    return p;
  }

  public Object visitExistsPred(ExistsPred p) {
    out.beginPrec(out.TIGHTEST);
    out.print("#");
    SchText stext = (SchText)p.getSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out.print(".");
    printPred(Create.andPred(types, p.getPred()));
    out.endPrec(out.TIGHTEST);
    return p;
  }

  public Object visitForallPred(ForallPred p) {
    out.beginPrec(out.TIGHTEST);
    out.print("!");
    SchText stext = (SchText)p.getSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out.print(".");
    printPred(Create.impliesPred(types, p.getPred()));
    out.endPrec(out.TIGHTEST);
    return p;
  }

  // Expressions
  public Object visitName(Name e) {
    out.printName(e);
    return e;
  }

  public Object visitNumExpr(NumExpr e) {
    out.print(e.getValue().toString());
    return e;
  }

  public Object visitApplExpr(ApplExpr e) {
    if (e.getMixfix().booleanValue()
	&& e.getRightExpr() instanceof TupleExpr
	&& e.getLeftExpr() instanceof RefExpr) {
      TupleExpr tuple = (TupleExpr)e.getRightExpr();
      RefExpr func = (RefExpr)e.getLeftExpr();
      // we ignore any type parameters
      if (tuple.getExpr().size() != 2)
	throw new BException("Cannot handle non-binary mixfix operator: "
			     + func);
      String opname = func.getRefName().getWord(); // TODO check no decorations
      // TODO: convert to B operator, if possible, else ???.
      infixOp(opname,
	      (Term)tuple.getExpr().get(0), 
	      (Term)tuple.getExpr().get(1));
    } else {
	infixOp("@", e.getLeftExpr(), e.getRightExpr());  //TODO fix!
    }
    return e;
  }

  public Object visitPowerExpr(PowerExpr e) {
    unaryFunc("POW", e.getExpr());
    return e;
  }



  // ================ unused  TODO: Add these? =======================
  public Object visitFreetype(Freetype zedObject) { 
    return zedObject;
  }

  public Object visitNameNamePair(NameNamePair zedObject) {
    return zedObject;
  }

  public Object visitLetExpr(LetExpr zedObject) {
    return zedObject;
  }

  public Object visitSignature(Signature zedObject) {
    return zedObject;
  }

  public Object visitConstDecl(ConstDecl zedObject) {
    return zedObject;
  }

  public Object visitProdType(ProdType zedObject) {
    return zedObject;
  }

  public Object visitDecl(Decl zedObject) {
    return zedObject;
  }

  public Object visitImpliesExpr(ImpliesExpr zedObject) {
    return zedObject;
  }

  public Object visitMuExpr(MuExpr zedObject) {
    return zedObject;
  }

  public Object visitSchExpr2(SchExpr2 zedObject) {
    return zedObject;
  }

  public Object visitExistsExpr(ExistsExpr zedObject) {
    return zedObject;
  }

  public Object visitExists1Expr(Exists1Expr zedObject) {
    return zedObject;
  }

  public Object visitForallExpr(ForallExpr zedObject) {
    return zedObject;
  }

  public Object visitVarDecl(VarDecl zedObject) {
    return zedObject;
  }

  public Object visitFreePara(FreePara zedObject) {
    return zedObject;
  }

  public Object visitCompExpr(CompExpr zedObject) {
    return zedObject;
  }

  public Object visitBindExpr(BindExpr zedObject) {
    return zedObject;
  }

  public Object visitCondExpr(CondExpr zedObject) {
    return zedObject;
  }

  public Object visitNameExprPair(NameExprPair zedObject) {
    return zedObject;
  }

  public Object visitTupleSelExpr(TupleSelExpr zedObject) {
    return zedObject;
  }

  public Object visitLambdaExpr(LambdaExpr zedObject) {
    return zedObject;
  }

  public Object visitIffExpr(IffExpr zedObject) {
    return zedObject;
  }

  public Object visitQntExpr(QntExpr zedObject) {
    return zedObject;
  }

  public Object visitUnparsedZSect(UnparsedZSect zedObject) {
    return zedObject;
  }

  public Object visitUnparsedPara(UnparsedPara zedObject) {
    return zedObject;
  }

  public Object visitNameTypePair(NameTypePair zedObject) {
    return zedObject;
  }

  public Object visitSchText(SchText zedObject) {
    return zedObject;
  }

  public Object visitQnt1Expr(Qnt1Expr zedObject) {
    return zedObject;
  }

  public Object visitOperand(Operand zedObject) {
    return zedObject;
  }

  public Object visitProjExpr(ProjExpr zedObject) {
    return zedObject;
  }

  public Object visitBranch(Branch zedObject) {
    return zedObject;
  }

  public Object visitGenType(GenType zedObject) {
    return zedObject;
  }

  public Object visitPara(Para zedObject) {
    return zedObject;
  }

  public Object visitOptempPara(OptempPara zedObject) {
    return zedObject;
  }

  public Object visitNameSectTypeTriple(NameSectTypeTriple zedObject) {
    return zedObject;
  }

  public Object visitExpr1(Expr1 zedObject) {
    return zedObject;
  }

  public Object visitPreExpr(PreExpr zedObject) {
    return zedObject;
  }

  public Object visitExprPred(ExprPred zedObject) {
    return zedObject;
  }

  public Object visitGivenType(GivenType zedObject) {
    return zedObject;
  }

  public Object visitInclDecl(InclDecl zedObject) {
    return zedObject;
  }

  public Object visitPred(Pred zedObject) {
    return zedObject;
  }

  public Object visitSchemaType(SchemaType zedObject) {
    return zedObject;
  }

  public Object visitBindSelExpr(BindSelExpr zedObject) {
    return zedObject;
  }

  public Object visitDeclName(DeclName zedObject) {
    return zedObject;
  }

  public Object visitOrExpr(OrExpr zedObject) {
    return zedObject;
  }

  public Object visitSpec(Spec zedObject) {
    return zedObject;
  }

  public Object visitHideExpr(HideExpr zedObject) {
    return zedObject;
  }

  public Object visitGivenPara(GivenPara zedObject) {
    return zedObject;
  }

  public Object visitPowerType(PowerType zedObject) {
    return zedObject;
  }

  public Object visitAndExpr(AndExpr zedObject) {
    return zedObject;
  }

  public Object visitRenameExpr(RenameExpr zedObject) {
    return zedObject;
  }

  public Object visitConjPara(ConjPara zedObject) {
    return zedObject;
  }

  public Object visitThetaExpr(ThetaExpr zedObject) {
    return zedObject;
  }

  public Object visitSetExpr(SetExpr zedObject) {
    return zedObject;
  }

  public Object visitSetCompExpr(SetCompExpr zedObject) {
    return zedObject;
  }

  public Object visitPipeExpr(PipeExpr zedObject) {
    return zedObject;
  }

  public Object visitRefExpr(RefExpr zedObject) {
    return zedObject;
  }

  public Object visitNegExpr(NegExpr zedObject) {
    return zedObject;
  }

  public Object visitProdExpr(ProdExpr zedObject) {
    return zedObject;
  }

  public Object visitDecorExpr(DecorExpr zedObject) {
    return zedObject;
  }

  public Object visitParent(Parent zedObject) {
    return zedObject;
  }

  public Object visitExists1Pred(Exists1Pred zedObject) {
    return zedObject;
  }

  public Object visitSchExpr(SchExpr zedObject) {
    return zedObject;
  }

  public Object visitTupleExpr(TupleExpr zedObject) {
    return zedObject;
  }
}
