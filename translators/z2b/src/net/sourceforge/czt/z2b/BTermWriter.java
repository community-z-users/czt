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
 * This class prints a Z predicate/expression out in B syntax.
 *
 * @author Mark Utting
 */
public class BTermWriter
  implements TermVisitor,
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
             PowerExprVisitor
{
  // Precedences of a few common B operators.
  // NOTE: these must agree with any matching entries in ops_.
  public static final int ASSIGN_PREC = -2;
  public static final int AND_PREC = -5;

  private BWriter out = null;

  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.z2b");
  
  /** This maps Z operators into B operators */
  private static Map ops_ = new HashMap();

  /** These objects store information about a B operator. */
  private class BOperator {
    String name;
    int arity; // number of arguments for this operator
    int prec;  // precedence of this operator
    BOperator(String bname, int barity, int bprec) {
      name = bname;
      arity = barity;
      prec = bprec;
    }

    /** This shorthand constructor is for unary (prefix) operators. */
    BOperator(String bname) {
      name = bname;
      arity = 1;
      prec = out.TIGHTEST;
    }
  }

  /** Get the B operator that corresponds to a Z operator, or null. */
  protected BOperator bOp(String zop) {
    String zname = zop;
    if (zop.length() == 1) {
      zname = "\\u" + Integer.toHexString((int)zop.charAt(0));
    }
    BOperator bop = (BOperator)ops_.get(zop);
    String bname = "null";
    if (bop != null)
      bname = bop.name + "/" + bop.arity;
    sLogger.fine("bOp("+zname+") returns "+bname);
    return bop;
  }

  /** Warning about any visitXXX methods that may not be called
  * because this class does not implement the associated interface.
  */
  public void checkVisitorRules() {
    Class c = this.getClass();
    java.lang.reflect.Method methods[] = c.getDeclaredMethods();
    Class interfaces[] = c.getInterfaces();
    for (int m=0; m<methods.length; m++) {
      String mname = methods[m].getName();
      if (mname.startsWith("visit")) {
        String iname = mname.substring(5) + "Visitor";
        boolean found = false;
        for (int i=0; i<interfaces.length && ! found; i++)
          found = interfaces[i].getName().endsWith(iname);
        if ( ! found) {
          System.err.println("Warning: class " + c.getName()
          + " should implement interface " + iname + "?");
        }
      }
    }
  }

  /**
   * Constructor for BWriteTerm
   *
   * @param dest Where to print the B predicates.
   *
   */
  public BTermWriter(BWriter dest) {
    out = dest;
    checkVisitorRules();
    
    // set up the operator translation table
    if (ops_.size() == 0) {
      // ============== unary prefix operators =============
      ops_.put("\u2119", new BOperator("POW"));
      ops_.put("dom",    new BOperator("dom"));
      ops_.put("ran",    new BOperator("ran"));
      ops_.put("min",    new BOperator("min"));
      ops_.put("max",    new BOperator("max"));
      ops_.put("\u22C3", new BOperator("Union")); // N-ary union
      ops_.put("\u22C2", new BOperator("Inter")); // N-ary intersection
      ops_.put("#",      new BOperator("card")); // set cardinality
      ops_.put("\u00AC", new BOperator("not")); // logical negation

      // ============== binary infix operators ================
      // ops_.put(".",   new BOperator(".", 2, 10));

      ops_.put("mod",    new BOperator("mod", 2, 3));
      ops_.put("*",      new BOperator("*", 2, 3));
      ops_.put("div",    new BOperator("/", 2, 3));
      ops_.put("\u00D7", new BOperator("*", 2, 3)); // cartesian product

      ops_.put("+",      new BOperator("+", 2, 2)); // multiplication
      ops_.put("\u2212", new BOperator("-", 2, 2)); // binary minus
      ops_.put("\\",     new BOperator("-", 2, 2)); // set minus prec=2?

      ops_.put("..",     new BOperator("..", 2, 1)); // integer range

      ops_.put("\u2229", new BOperator("/\\", 2, 0));  // intersection
      ops_.put("\u222A", new BOperator("\\/", 2, 0));  // union
      ops_.put("\u21A6", new BOperator("|->", 2, 0)); // maps-to
      ops_.put("\u25C1", new BOperator("<|", 2, 0)); // domain restriction
      ops_.put("\u2A64", new BOperator("<<|", 2, 0)); // domain substraction
      ops_.put("\u25B7", new BOperator("|>", 2, 0)); // range restriction
      ops_.put("\u2A65", new BOperator("|>>", 2, 0)); // range subtraction
      ops_.put("\u2295", new BOperator("<+", 2, 0)); // reln. override
      // ops_.put("+>",  new BOperator("+>", 2, 0));
      // ops_.put("><",  new BOperator("><", 2, 0));
      // ops_.put("circ",new BOperator("circ", 2, 0));
      ops_.put("\u2040", new BOperator("^", 2, 0)); // seq. concatenation
      // ops_.put("->",  new BOperator("->", 2, 0));
      // ops_.put("<-",  new BOperator("<-", 2, 0));
      // ops_.put("/|\\",new BOperator("/|\\", 2, 0));
      // ops_.put("\\|/",new BOperator("\\|/", 2, 0));
      ops_.put("<",      new BOperator("<", 2, 0)); // integer less than
      ops_.put("\u2264", new BOperator("<=", 2, 0)); // int. less or equals
      ops_.put(">",      new BOperator(">", 2, 0)); // int. greater than
      ops_.put("\u2265", new BOperator(">=", 2, 0)); // int. greater or equal
      ops_.put("\u2260", new BOperator("/=", 2, 0));  // not equal to
      ops_.put("\u2209", new BOperator("/:", 2, 0));  // not an element of

      ops_.put("\u2194", new BOperator("<->", 2, -1)); // relation
      ops_.put("\u2192", new BOperator("-->", 2, -1)); // total func
      ops_.put("\u21F8", new BOperator("+->", 2, -1)); // partial func
      ops_.put("\u21A3", new BOperator(">->", 2, -1)); // total injection
      ops_.put("\u2914", new BOperator(">+>", 2, -1)); // partial injection
      ops_.put("\u2900", new BOperator("+->>", 2, -1)); // partial surjection
      ops_.put("\u2916", new BOperator(">->>", 2, -1)); // total bijection
      ops_.put("\u21A0", new BOperator("-->>", 2, -1)); // total surjection
      // ops_.put("<--", new BOperator("<--", 2, -1));
      ops_.put(",",      new BOperator(",", 2, -1)); // pairs/tuples
      // NOTE: we treat finite functions/bijections as being identical
      //     to partial functions/bijections, since all types are finite in B
      ops_.put("\u21FB", new BOperator("+->", 2, -1)); // partial func
      ops_.put("\u2915", new BOperator(">+>", 2, -1)); // partial injection

      ops_.put("\u2286", new BOperator("<:", 2, -2)); // subset of or equal to
      ops_.put("\u2282", new BOperator("<<:", 2, -2)); // subset of
      // ops_.put("/<:", new BOperator("/<:", 2, -2));
      // ops_.put("/<<:",new BOperator("/<<:", 2, -2));
      // ops_.put(":=",  new BOperator(":=", 2, -2));

      ops_.put("=",      new BOperator("=", 2, -4));  // equal to
      // ops_.put("==",  new BOperator("==", 2, -4));
      ops_.put("\u2208", new BOperator(":", 2, -4));  // membership
      ops_.put("\u21D4", new BOperator("<=>", 2, -4)); // TODO check prec
      // ops_.put("::",  new BOperator("::", 2, -4));

      // assert AND_PREC == -5;
      ops_.put("\u2227", new BOperator("&", 2, -5));
      ops_.put("\u2228", new BOperator("or", 2, -5));

      ops_.put("\u21D2",  new BOperator("=>", 2, -6));
      // ops_.put("==>", new BOperator("==>", 2, -6));

      // ops_.put("\u2A3E",   new BOperator(";", 2, -7)); // reln. composition?
      // ops_.put("||",  new BOperator("||", 2, -7));
      // ops_.put("[]",  new BOperator("[]", 2, -7));

      // ops_.put("|",   new BOperator("|", 2, -8));
    }
  }


  /** Print a list of predicates, separated by '&' and newlines.
   *  <esc> requires preds.size() > 0 </esc>
   */
  public void printPreds(List preds) {
    out.beginPrec(AND_PREC);
    Iterator i = preds.iterator();
    // assert i.hasNext();
    while (true) {
      Pred p = (Pred)i.next();
      printPred(p);
      if ( ! i.hasNext())
	break;
      out.printSeparator(" & ");
    }
    out.endPrec(AND_PREC);
  }

  /** Print a single Z predicate out in B syntax.
   *  The priority of the surrounding context of the predicate 
   *  should be set by the caller if necessary.  Usually the
   *  current context is sufficient.
   */
  public void printPred(Pred p) {
      sLogger.fine("printing Pred: " + p);    
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
   *  @param bOp      The B name of the function
   *  @param arg      The argument predicate/expression
   */
   //@ requires bOp != null;
   //@ requires bOp.arity == 1;
   //@ requires arg != null;
  protected void unaryOp(BOperator bOp, Term arg) {
    sLogger.entering("BTermWriter","unaryOp");
    out.beginPrec(out.TIGHTEST);
    out.print(bOp.name);
    // beginPrec will add the opening "(".
    out.beginPrec(out.LOOSEST);
    arg.accept(this);
    // endPrec will add the closing "(".
    out.endPrec(out.LOOSEST);
    out.endPrec(out.TIGHTEST);
    sLogger.exiting("BTermWriter","unaryOp");
  }


  /** This handles all infix operators (except '.').
   *  @param bOp  The B name of the binary operator
   *  @param left   Left predicate/expression
   *  @param right  Right predicate/expression
   *  All B infix operators (except '.') are left associative.
   */
   //@ requires bOp != null;
   //@ requires left != null;
   //@ requires right != null;
   //@ requires bOp.arity == 2;
  protected void infixOp(BOperator bOp, Term left, Term right) {
    sLogger.entering("BTermWriter","infixOp");
    int prec = bOp.prec;
    out.beginPrec(prec);

    left.accept(this);
    out.print(" " + bOp.name + " ");

    // Now process the right arg at a lower precedence.
    out.beginPrec(prec+1);
    right.accept(this);
    out.endPrec(prec+1);
      
    out.endPrec(prec);
    sLogger.exiting("BTermWriter","infixOp");
  }


  /* =============================================
     The visitor methods.
     These all write output via the BWriter object.
     They do not change the AST they are visiting.
     =============================================
  */
  
  /** This generic visit method recurses into all Z terms. */
  public Object visitTerm(Term term) {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Object visitAndPred(AndPred p) {
    infixOp(bOp("\u2227"), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitOrPred(OrPred p) {
    infixOp(bOp("\u2228"), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitImpliesPred(ImpliesPred p) {
    infixOp(bOp("\u21D2"), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitIffPred(IffPred p) {
    infixOp(bOp("\u21D4"), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitNegPred(NegPred p) {
    unaryOp(bOp("\u00AC"), p.getPred());
    return p;
  }

  public Object visitMemPred(MemPred p) {
    BOperator op = null;
    if ( //p.getMixfix().booleanValue()
    p.getLeftExpr() instanceof TupleExpr) {
      // Try to map the relation to a B operator.
      if (p.getRightExpr() instanceof RefExpr) {
        RefExpr func = (RefExpr)p.getRightExpr();
        RefName name = func.getRefName();
        if (name.getStroke().size() == 0) {
          String zop = name.getWord();
          op = bOp(zop);
          sLogger.fine("MemPred(" + zop + ") --> B " + op);
        }
      }
    }
    if (op != null) {
      if (op.arity == 1) {
        unaryOp(op, p.getLeftExpr());
      } else if (op.arity == 2) {
        if ( ! (p.getLeftExpr() instanceof TupleExpr))
          throw new BException(op.name + " applied to non-tuple");
        List pair = ((TupleExpr)p.getLeftExpr()).getExpr();
        if (pair.size() != 2) {
          throw new BException("B " + op.name + " applied to "
          + pair.size() + " args.");
        }
        infixOp(op, (Expr)pair.get(0), (Expr)pair.get(1));
      } else {
        throw new BException("internal error: " + op.name 
        + " has illegal arity " + op.arity);
      }
    } else {
      infixOp(bOp("\u2208"), p.getLeftExpr(), p.getRightExpr());
    }
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


  //=========================================================
  // Expressions
  //=========================================================
  public Object visitName(Name e) {
    out.printName(e);
    return e;
  }

  public Object visitNumExpr(NumExpr e) {
    out.print(e.getValue().toString());
    return e;
  }

  public Object visitApplExpr(ApplExpr e) {
    // Try to map the function to a B operator.
    BOperator op = null;
    if (e.getLeftExpr() instanceof RefExpr) {
      RefExpr func = (RefExpr)e.getLeftExpr();
      RefName name = func.getRefName();
      if (name.getStroke().size() == 0) {
	String zop = name.getWord();
	op = bOp(zop);
        sLogger.fine("ApplExpr(" + zop + ") --> B " + op);
      }
    }
    if (op != null) {
      if (op.arity == 1) {
        unaryOp(op, e.getRightExpr());
      } else if (op.arity == 2) {
        if ( ! (e.getRightExpr() instanceof TupleExpr))
          throw new BException(op.name + " applied to non-tuple");
        List pair = ((TupleExpr)e.getRightExpr()).getExpr();
        if (pair.size() != 2) {
          throw new BException("B " + op.name + " applied to "
          + pair.size() + " args.");
        }
        infixOp(op, (Expr)pair.get(0), (Expr)pair.get(1));
      } else {
        throw new BException("internal error: " + op.name 
          + " has illegal arity " + op.arity);
      }
    } else {
      // Print:  left(right)
      out.beginPrec(out.TIGHTEST);
      e.getLeftExpr().accept(this);
      // beginPrec will add the opening "(".
      out.beginPrec(out.LOOSEST);
      e.getRightExpr().accept(this);
      // endPrec will add the closing "(".
      out.endPrec(out.LOOSEST);
      out.endPrec(out.TIGHTEST);
    }
    return e;
  }

  public Object visitRefExpr(RefExpr e) {
    BOperator op = null;
    RefName name = e.getRefName();
    if (name.getStroke().size() == 0) 
      op = bOp(name.getWord());
    if (op != null && op.arity == e.getExpr().size()) {
      if (op.arity == 1) {
        unaryOp(op, (Expr)e.getExpr().get(0));
      } else {
        infixOp(op, (Expr)e.getExpr().get(0), (Expr)e.getExpr().get(1));
      }
    } else {
      name.accept(this);
    }
    return e;
  }

  public Object visitPowerExpr(PowerExpr e) {
    BOperator op = bOp("\u2119");
    sLogger.fine("printing PowerExpr.  op=" + op);    
    unaryOp(op, e.getExpr());
    return e;
  }


/*
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
*/
}
