/**
Copyright 2003 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z2bzp;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z2bzp.*;

/**
 * <p>This class writes a Z term out in BZP syntax.
 *
 * BZP is the Prolog-readable syntax used as an input format for the
 * "BZ Testing Tools" (BZ-TT) Environment.
 *
 * @author Mark Utting
 */
public class BzpTranslator
  extends AstTermVisitor
  implements ZSectVisitor,
	     AxParaVisitor,

	     AndPredVisitor,
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
  // Some constants for the various Prolog associativities.
  // (This should really be an enumeration).
  private static final int FX  = 21;
  private static final int FY  = 22;
  private static final int XFX = 121;
  private static final int YFX = 221;
  private static final int XFY = 122;


  private BzpWriter bzp = null;
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.z2bzp");


  /**
   * Constructor for BzpWriter
   *
   * @param dest where to print the BZP predicates.
   *
   */
  public BzpTranslator(BzpWriter dest) {
    bzp = dest;
  }


  /** This handles all unary functions:   foo(Arg).
   *  @param bzpFunc  The BZP name of the function
   *  @param arg      The argument predicate/expression
   */
  public void unaryFunc(String bzpFunc, Term arg) {
    bzp.beginPrec(0);
    bzp.print(bzpFunc);
    // beginPrec will add the opening "(".
    bzp.beginPrec(bzp.MAXPREC);
    arg.accept(this);
    // endPrec will add the closing "(".
    bzp.endPrec(bzp.MAXPREC);
    bzp.endPrec(0);
  }


  /** This handles all infix operators.
   *  @param bzpOp  The BZP name of the binary operator
   *  @param prec   Precedence of the operator
   *  @param assoc  Must be XFX, XFY or YFX (like in Prolog)
   *  @param left   Left predicate/expression
   *  @param right  Right predicate/expression
   */
  public void infixOp(String bzpOp, int prec, int assoc,
		      Term left, Term right) {
    bzp.beginPrec(prec);

    // Now process the left arg, possibly at a lower precedence.
    if (assoc == YFX) {
      left.accept(this);
    }
    else {
      bzp.beginPrec(prec-1);
      left.accept(this);
      bzp.endPrec(prec-1);
    }
      
    bzp.print(" " + bzpOp + " ");

    // Now process the right arg, possibly at a lower precedence.
    if (assoc == XFY) {
      right.accept(this);
    }
    else {
      bzp.beginPrec(prec-1);
      right.accept(this);
      bzp.endPrec(prec-1);
    }
      
    bzp.endPrec(prec);
  }


  /* =============================================
     The visitor methods.
     These all write output via the emit* and begin/end* methods.
     They do not change the AST they are visiting.
     =============================================
  */


  /**
   * Output one section in BZP format.
   *
   * @param zedObject the section to be output.
   *   This records the section name for later use.
   */
  public Object visitZSect(ZSect sect) {
    bzp.printSpecFact(sect.getName());
    visitList(sect.getPara());
    return sect;
  }

  public Object visitAxPara(AxPara axpara) {
    sLogger.entering("BzpWriter","visitAxPara",axpara);
    List decls = axpara.getSchText().getDecl();
    // TODO: recognise/classify schema decls...
    if (decls.size() == 1
	&& decls.get(0) instanceof ConstDecl) {
      ConstDecl cdecl = (ConstDecl) decls.get(0);
      String opName = bzp.bzpName(cdecl.getDeclName());
      bzp.printOpFact(opName);
      // Now recurse into the schema...
      cdecl.getExpr().accept(this);
      // TODO: emit the input and output decls, pre, post etc.
    }
    sLogger.exiting("BzpWriter","visitAxPara",axpara);
    return axpara;
  }


  public Object visitAndPred(AndPred p) {
    infixOp("and", 800, YFX, p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitOrPred(OrPred p) {
    infixOp("or", 800, YFX, p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitImpliesPred(ImpliesPred p) {
    infixOp("=>", 850, YFX, p.getLeftPred(), p.getRightPred());
    return p;
  }

  /** @todo  check that this DOES have precedence 700, XFX?
   */
  public Object visitIffPred(IffPred p) {
    infixOp("<=>", 700, XFX, p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitNegPred(NegPred p) {
    unaryFunc("not", p.getPred());
    return p;
  }

  public Object visitMemPred(MemPred p) {
    infixOp(":", 700, XFX, p.getLeftExpr(), p.getRightExpr());
    return p;
  }

  public Object visitFalsePred(FalsePred p) {
    bzp.print("false");
    return p;
  }

  public Object visitTruePred(TruePred p) {
    bzp.print("true");
    return p;
  }



  // Expressions
  public Object visitName(Name e) {
    bzp.print(bzp.bzpName(e));
    return e;
  }

  public Object visitNumExpr(NumExpr e) {
    bzp.print(e.getValue().toString());
    return e;
  }

  public Object visitApplExpr(ApplExpr e) {
      infixOp("@", 1, XFX, e.getLeftExpr(), e.getRightExpr());  //TODO check
    return e;
  }

  public Object visitPowerExpr(PowerExpr e) {
    unaryFunc("pow", e.getExpr());
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

  public Object visitExistsPred(ExistsPred zedObject) {
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

  public Object visitForallPred(ForallPred zedObject) {
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
