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
import net.sourceforge.czt.z.util.ZString;

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
             PowerExprVisitor,
             SetExprVisitor,
             ProdExprVisitor,
             TupleExprVisitor
{
  // Precedences of a few common B operators.
  // NOTE: these must agree with any matching entries in ops_.
  public static final int ASSIGN_PREC = -2;
  public static final int DEFN_PREC = -4;
  public static final int COMMA_PREC = -1;
  public static final int AND_PREC = -5;
  protected static final String arg = " _ "; // indicates arg of an operator 

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

    /** Prints the B operator as a string */
    public String toString() {
      return name + "/" + arity;
    }
  }

  /** Add a prefix operator to the ops_ table */
  protected void addPrefix(String zop, String bop )
  {
    ops_.put(zop+" _ ", new BOperator(bop));
  }

  /** Add an infix operator to the ops_ table */
  protected void addInfix(String zop, String bop, int bprec)
  {
    ops_.put(" _ "+zop+" _ ", new BOperator(bop, 2, bprec));
  }

  /** Get the B operator that corresponds to a Z operator, or null. */
  protected BOperator bOp(String zop) {
    BOperator bop = (BOperator)ops_.get(zop);

    // generate a log message
    String zname = zop;
    if (zop.length() == 1)
      zname = "\\u" + Integer.toHexString((int)zop.charAt(0));
    sLogger.fine("bOp("+zname+") returns "+bop);
    return bop;
  }

  /**
   * Constructor for BWriteTerm
   *
   * @param dest Where to print the B predicates.
   *
   */
  public BTermWriter(BWriter dest) {
    VisitorUtils.checkVisitorRules(this);
    out = dest;
    
    // set up the operator translation table
    if (ops_.size() == 0) {
      // ============== unary prefix operators =============
      addPrefix("\u2119", "POW");
      ops_.put("dom",    new BOperator("dom"));  // not an operator
      ops_.put("ran",    new BOperator("ran"));  // not an operator
      addPrefix("min",    "min");
      addPrefix("max",    "max");
      addPrefix("\u22C3", "Union"); // N-ary union
      addPrefix("\u22C2", "Inter"); // N-ary intersection
      addPrefix("#",      "card"); // set cardinality
      addPrefix("\u00AC", "not"); // logical negation

      // ============== binary infix operators ================
      // addInfix(".",   ".", 10);

      addInfix("mod",    "mod", 3);
      addInfix("*",      "*", 3);
      addInfix("div",    "/", 3);
      addInfix("\u00D7", "*", 3); // cartesian product

      addInfix("+",      "+", 2); // multiplication
      addInfix("\u2212", "-", 2); // binary minus
      addInfix("\\",     "-", 2); // set minus prec=2?

      addInfix("..", "..", 1); // integer range

      addInfix("\u2229", "/\\",  0);  // intersection
      addInfix("\u222A", "\\/", 0);  // union
      addInfix("\u21A6", "|->", 0); // maps-to
      addInfix("\u25C1", "<|", 0); // domain restriction
      addInfix("\u2A64", "<<|", 0); // domain substraction
      addInfix("\u25B7", "|>", 0); // range restriction
      addInfix("\u2A65", "|>>", 0); // range subtraction
      addInfix("\u2295", "<+", 0); // reln. override
      // addInfix("+>",  "+>", 0);
      // addInfix("><",  "><", 0);
      // addInfix("circ","circ", 0);
      addInfix("\u2040", "^", 0); // seq. concatenation
      // addInfix("->",  "->", 0);
      // addInfix("<-",  "<-", 0);
      // addInfix("/|\\","/|\\", 0);
      // addInfix("\\|/","\\|/", 0);
      addInfix("<",      "<", 0); // integer less than
      addInfix("\u2264", "<=", 0); // int. less or equals
      addInfix(">",      ">", 0); // int. greater than
      addInfix("\u2265", ">=", 0); // int. greater or equal
      addInfix("\u2260", "/=", 0);  // not equal to
      addInfix("\u2209", "/:", 0);  // not an element of

      addInfix("\u2194", "<->", -1); // relation
      addInfix("\u2192", "-->", -1); // total func
      addInfix("\u21F8", "+->", -1); // partial func
      addInfix("\u21A3", ">->", -1); // total injection
      addInfix("\u2914", ">+>", -1); // partial injection
      addInfix("\u2900", "+->>", -1); // partial surjection
      addInfix("\u2916", ">->>", -1); // total bijection
      addInfix("\u21A0", "-->>", -1); // total surjection
      // addInfix("<--", "<--", -1);
      addInfix(",",      "|->", -1); // pairs/tuples
      // NOTE: we treat finite functions/bijections as being identical
      //     to partial functions/bijections, since all types are finite in B
      addInfix("\u21FB", "+->", -1); // partial func
      addInfix("\u2915", ">+>", -1); // partial injection

      addInfix("\u2286", "<:", -2); // subset of or equal to
      addInfix("\u2282", "<<:", -2); // subset of
      // addInfix("/<:", "/<:", -2);
      // addInfix("/<<:","/<<:", -2);
      // addInfix(":=",  ":=", -2);

      addInfix("=",      "=", -4);  // equal to
      // addInfix("==",  "==", -4);
      addInfix("\u2208", ":", -4);  // membership
      addInfix("\u21D4", "<=>", -4); // TODO check prec
      // addInfix("::",  "::", -4);

      // assert AND_PREC == -5;
      addInfix("\u2227", "&", -5);
      addInfix("\u2228", "or", -5);

      addInfix("\u21D2",  "=>", -6);
      // addInfix("==>", "==>", -6);

      // addInfix("\u2A3E",   ";", -7); // reln. composition?
      // addInfix("||",  "||", -7);
      // addInfix("[]",  "[]", -7);

      // addInfix("|",   "|", -8);
    }
  }

  
  /** Print a non-deterministic update of some variables, 
  *   given some predicates.
  *   @param frame  The (var,expr) pairs to put in the assignments.
  *   @param preds  The predicates that the expressions must satisfy.
  */
  public void printAnyAssign(Map frame, List preds) {
    // now print the ANY..WHERE..THEN..END statement.
    out.startSection("ANY");
    // print the temporary names (like printNames, but for RefNames)
    for (Iterator i = frame.values().iterator(); i.hasNext(); ) {
      RefName name = (RefName)i.next();
      out.printName(name);
      if (i.hasNext())
        out.print(",");
    }
    out.continueSection("ANY", "WHERE");
    out.printPreds(preds);
    out.continueSection("ANY", "THEN");
    for (Iterator i = frame.entrySet().iterator(); i.hasNext(); ) {
      Map.Entry entry = (Map.Entry)i.next();
      String name = (String)entry.getKey();
      RefName tempname = (RefName)entry.getValue();
      // output the assignment name := tempname
      out.beginPrec(BTermWriter.ASSIGN_PREC);
      out.printName(name);
      out.print(" := ");
      out.printName(tempname);
      out.endPrec(BTermWriter.ASSIGN_PREC);
      if (i.hasNext())
        out.printSeparator(" || ");
    }
    out.endSection("END");
  }


  /** Print a list of predicates, separated by '&' and newlines. */
  //@ requires preds != null && preds.size() > 0;
  public void printPreds(List preds) {
    out.beginPrec(AND_PREC);
    Iterator i = preds.iterator();
    assert i.hasNext();
    while (i.hasNext()) {
      Pred p = (Pred)i.next();
      printPred(p);
      if (i.hasNext())
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
  //@ requires s != null;
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
    infixOp(bOp(arg+ZString.AND+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitOrPred(OrPred p) {
    infixOp(bOp(arg+ZString.OR+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitImpliesPred(ImpliesPred p) {
    infixOp(bOp(arg+ZString.IMP+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitIffPred(IffPred p) {
    infixOp(bOp(arg+ZString.IFF+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Object visitNegPred(NegPred p) {
    unaryOp(bOp(ZString.NOT+arg), p.getPred());
    return p;
  }

  public Object visitMemPred(MemPred p) {
    BOperator op = null;
    if (p.getMixfix().booleanValue()
	&& p.getRightExpr() instanceof SetExpr
	&& ((SetExpr)p.getRightExpr()).getExpr().size() == 1) {
      Expr left = p.getLeftExpr();
      Expr right = (Expr) ((SetExpr)p.getRightExpr()).getExpr().get(0);
      infixOp(bOp(arg+"="+arg), left, right);
      return p;
    }
    if (p.getMixfix().booleanValue()) {
      // Try to map the relation to a B operator.
      if (p.getRightExpr() instanceof RefExpr) {
        RefExpr func = (RefExpr)p.getRightExpr();
        RefName name = func.getRefName();
        if (name.getStroke().size() == 0) {
	  // NOTE: we ignore any type arguments here., assuming
	  // that they were added by the typechecking.
	  // This should be the case when Mixfix=true.
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
      infixOp(bOp(arg+ZString.MEM+arg), p.getLeftExpr(), p.getRightExpr());
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
    out.print("#(");
    SchText stext = (SchText)p.getSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out.print(").");
    printPred(Create.andPred(types, p.getPred()));
    out.endPrec(out.TIGHTEST);
    return p;
  }

  public Object visitForallPred(ForallPred p) {
    out.beginPrec(out.TIGHTEST);
    out.print("!(");
    SchText stext = (SchText)p.getSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out.print(").");
    printPred(Create.impliesPred(types, p.getPred()));
    out.endPrec(out.TIGHTEST);
    return p;
  }


  //=========================================================
  // Expressions
  //=========================================================
  public Object visitName(Name e) {
    String zName = Create.stringName(e);
    sLogger.fine("BTermWriter.visitName(" + e + ") sees " + zName);
    // Now check for various B constants
    if (zName.equals(ZString.EMPTYSET))
      out.print("{}");
    else if (zName.equals(ZString.NAT))
      out.print("NAT");
    else if (zName.equals(ZString.NAT + "_1"))
      out.print("NAT1");
    else if (zName.equals(ZString.NUM))
      out.print("INT");
    else
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
    sLogger.fine("RefExpr(" + name.getWord() + "...) --> B " + op);
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
    BOperator op = bOp(ZString.POWER+arg);
    sLogger.fine("printing PowerExpr.  op=" + op);    
    unaryOp(op, e.getExpr());
    return e;
  }

  public Object visitSetExpr(SetExpr set) {
    out.beginPrec(out.TIGHTEST);
    out.print("{");
    out.beginPrec();
    out.beginPrec(COMMA_PREC);
    for (Iterator i = set.getExpr().iterator(); i.hasNext(); ) {
      out.printExpr((Expr)i.next());
      if (i.hasNext())
        out.print(", ");
    }
    out.endPrec(COMMA_PREC);
    out.endPrec();
    out.print("}");
    out.endPrec(out.TIGHTEST);
    return set;
  }

  public Object visitProdExpr(ProdExpr e) {
    List sets = e.getExpr();
    if (sets.size() == 2) {
      infixOp(bOp(arg+ZString.CROSS+arg), 
	      (Expr)sets.get(0),
	      (Expr)sets.get(1));
    }
    else {
      // construct a right associative tree of binary cartesian products
      assert sets.size() > 2;
      int last = sets.size() - 1;
      Expr prod = (Expr)sets.get(last);
      for ( ; last >= 0; last--)
	prod = Create.binaryprod((Expr)sets.get(last), prod);
      visitProdExpr((ProdExpr)prod);
    }
    return e;
  }

  public Object visitTupleExpr(TupleExpr e) {
    List sets = e.getExpr();
    if (sets.size() == 2) {
      infixOp(bOp(arg+","+arg), 
	      (Expr)sets.get(0),
	      (Expr)sets.get(1));
    }
    else {
      // construct a right associative tree of binary cartesian products
      assert sets.size() > 2;
      int last = sets.size() - 1;
      Expr pair = (Expr)sets.get(last);
      for ( ; last >= 0; last--)
	pair = Create.pair((Expr)sets.get(last), pair);
      visitTupleExpr((TupleExpr)pair);
    }
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
*/
}
