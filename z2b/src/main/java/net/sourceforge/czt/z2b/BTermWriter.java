/**
Copyright 2003, 2006 Mark Utting
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
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * This class prints a Z predicate/expression out in B syntax.
 *
 * @author Mark Utting
 */
public class BTermWriter
  implements TermVisitor<Term>,
             AndPredVisitor<Term>,
	     OrPredVisitor<Term>,
	     ImpliesPredVisitor<Term>,
	     IffPredVisitor<Term>,
	     NegPredVisitor<Term>,
	     MemPredVisitor<Term>,
	     FalsePredVisitor<Term>,
	     TruePredVisitor<Term>,
             ExistsPredVisitor<Term>,
             ForallPredVisitor<Term>,

	     ZNameVisitor<Term>,
	     NumExprVisitor<Term>,
	     ApplExprVisitor<Term>,
             LambdaExprVisitor<Term>,
             RefExprVisitor<Term>,
             PowerExprVisitor<Term>,
             SetCompExprVisitor<Term>,
             SetExprVisitor<Term>,
             ProdExprVisitor<Term>,
             TupleExprVisitor<Term>
{
  // Precedences of a few common B operators.
  // NOTE: these must agree with any matching entries in ops_.
  public static final int ASSIGN_PREC = -2;
  public static final int DEFN_PREC = -4;
  public static final int COMMA_PREC = -1;
  public static final int AND_PREC = -5;
  protected static final String arg = " _ "; // indicates arg of an operator 

  private BWriter out_ = null;

  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.z2b");
  
  /** This maps Z operators into B operators */
  private static Map<String,BOperator> ops_ =
    new HashMap<String,BOperator>();

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
      prec = out_.TIGHTEST;
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
    out_ = dest;
    
    // Set up the operator translation table
    // This uses the precedences (-10..+10) defined in the B Toolkit
    // (where higher numbers mean tighter binding).
    // See http://www.b-core.com/ONLINEDOC/MathsNotation.html
    //
    // NOTE: Atelier B has different precedence numbers (0..250), but the
    // relationships between operators are the same, except for a few
    // cases like : and <: which are reversed -- but such cases never
    // arise in practice because these two operators never appear together.
    // So I think that the B generated by this class will be compatible
    // with both the B-Core B toolkit and Atelier B.
    if (ops_.size() == 0) {
      // ============== unary prefix operators =============
      addPrefix("\u2119", "POW");
      addPrefix("\u0001\uD53D", "POW");
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

      addInfix("\u2A3E",   ";", -7); // reln. comp. and sequencing.
      // addInfix("||",  "||", -7);
      // addInfix("[]",  "[]", -7);

      // addInfix("|",   "|", -8);
    }
  }

  private Factory getFactory()
  {
    return Create.getFactory();
  }
  
  /** Print a non-deterministic update of some variables, 
  *   given some predicates.
  *   @param frame  The (var,expr) pairs to put in the assignments.
  *   @param preds  The predicates that the expressions must satisfy.
  */
  public void printAnyAssign(Map<String,ZName> frame, List<Pred> preds) {
    // now print the ANY..WHERE..THEN..END statement.
    out_.startSection("ANY");
    // print the temporary names (like printNames, but for Names)
    for (Iterator<ZName> i = frame.values().iterator(); i.hasNext(); ) {
      ZName name = i.next();
      out_.printName(name);
      if (i.hasNext()) out_.print(",");
    }
    out_.continueSection("ANY", "WHERE");
    out_.printPreds(preds);
    out_.continueSection("ANY", "THEN");
    for (Iterator<Map.Entry<String,ZName>> i = frame.entrySet().iterator();
         i.hasNext(); ) {
      Map.Entry<String,ZName> entry = i.next();
      String name = entry.getKey();
      ZName tempname = entry.getValue();
      // output the assignment name := tempname
      out_.beginPrec(BTermWriter.ASSIGN_PREC);
      out_.printName(name);
      out_.print(" := ");
      out_.printName(tempname);
      out_.endPrec(BTermWriter.ASSIGN_PREC);
      if (i.hasNext()) out_.printSeparator(" || ");
    }
    out_.endSection("ANY");
  }


  /** Print a list of predicates, separated by '&' and newlines. */
  //@ requires preds != null && preds.size() > 0;
  //  requires non_null_elements(preds);
  public void printPreds(List preds)
  {
    out_.beginPrec(AND_PREC+1);
    Iterator i = preds.iterator();
    assert i.hasNext();
    while (i.hasNext()) {
      Pred p = (Pred)i.next();
      assert p != null;
      printPred(p);
      if (i.hasNext())
        out_.printSeparator(" & ");
    }
    out_.endPrec(AND_PREC+1);
  }

  /** Print a single Z predicate out in B syntax.
   *  The priority of the surrounding context of the predicate 
   *  should be set by the caller if necessary.  Usually the
   *  current context is sufficient.
   */
  public void printPred(Pred p)
  {
    sLogger.fine("printing Pred: " + p);    
    p.accept(this);
  }

  /** Print a Z expression out in B syntax.
   *  The priority of the surrounding context of the predicate 
   *  should be set by the caller if necessary.
   */
  public void printExpr(Expr e)
  {
    e.accept(this);
  }



  //================== Auxiliary functions ===================

  /** This prints a comma-separated list of all the names in a SchText,
   *  and returns the associated type conditions as one predicate.
   */
  //@ requires s != null;
  protected Pred splitSchText(ZSchText s)
  {
    Pred result = null;
    for (Decl d : s.getZDeclList()) {
      if (d instanceof VarDecl) {
	VarDecl vdecl = (VarDecl) d;
        for (Name name : vdecl.getName()) {
	  ZName declName = (ZName) name;
          ZName refName = getFactory().createZName(declName);
	  Pred ntype = getFactory().createMemPred(refName, vdecl.getExpr());
	  if (result == null) {
	    result = ntype;
	  }
          else {
	    out_.print(",");
	    result = Create.andPred(result,ntype);
	  }
	  out_.printName(declName);
	}
      } else if (d instanceof ConstDecl) {
	ConstDecl cdecl = (ConstDecl)d;
	ZName n = cdecl.getZName();
	Pred ntype = Create.eqPred(n, cdecl.getExpr());
	if (result == null) {
	  result = ntype;
	}
        else {
	  out_.print(",");
	  result = Create.andPred(result,ntype);
	}
	out_.printName(n);
      }
      else {
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
  protected void unaryOp(BOperator bOp, Term arg)
  {
    sLogger.entering("BTermWriter","unaryOp");
    out_.beginPrec(out_.TIGHTEST);
    out_.print(bOp.name);
    // beginPrec will add the opening "(".
    out_.beginPrec(out_.LOOSEST);
    arg.accept(this);
    // endPrec will add the closing "(".
    out_.endPrec(out_.LOOSEST);
    out_.endPrec(out_.TIGHTEST);
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
  protected void infixOp(BOperator bOp, Term left, Term right)
  {
    sLogger.entering("BTermWriter","infixOp");
    int prec = bOp.prec;
    out_.beginPrec(prec);

    left.accept(this);
    out_.print(" " + bOp.name + " ");

    // Now process the right arg at a lower precedence.
    out_.beginPrec(prec+1);
    right.accept(this);
    out_.endPrec(prec+1);
      
    out_.endPrec(prec);
    sLogger.exiting("BTermWriter","infixOp");
  }


  /* =============================================
     The visitor methods.
     These all write output via the BWriter object.
     They do not change the AST they are visiting.
     =============================================
  */
  
  /** This generic visit method recurses into all Z terms. */
  public Term visitTerm(Term term)
  {
    final String msg = "BTermWriter does not yet support " + term.toString();
    throw new UnsupportedOperationException(msg);
  }

  public Term visitAndPred(AndPred p)
  {
    infixOp(bOp(arg+ZString.AND+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Term visitOrPred(OrPred p)
  {
    infixOp(bOp(arg+ZString.OR+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Term visitImpliesPred(ImpliesPred p)
  {
    infixOp(bOp(arg+ZString.IMP+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Term visitIffPred(IffPred p)
  {
    infixOp(bOp(arg+ZString.IFF+arg), p.getLeftPred(), p.getRightPred());
    return p;
  }

  public Term visitNegPred(NegPred p)
  {
    unaryOp(bOp(ZString.NOT+arg), p.getPred());
    return p;
  }

  public Term visitMemPred(MemPred p)
  {
    BOperator op = null;
    if (p.getMixfix().booleanValue()
	&& p.getRightExpr() instanceof SetExpr
	&& ((SetExpr)p.getRightExpr()).getZExprList().size() == 1) {
      Expr left = p.getLeftExpr();
      Expr right = ((SetExpr)p.getRightExpr()).getZExprList().get(0);
      infixOp(bOp(arg+"="+arg), left, right);
      return p;
    }
    if (p.getMixfix().booleanValue()) {
      // Try to map the relation to a B operator.
      if (p.getRightExpr() instanceof RefExpr) {
        RefExpr func = (RefExpr)p.getRightExpr();
        ZName name = func.getZName();
        if (! hasDecorations(name)) {
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
        List<Expr> pair = ((TupleExpr)p.getLeftExpr()).getZExprList();
        if (pair.size() != 2) {
          throw new BException("B " + op.name + " applied to "
          + pair.size() + " args.");
        }
        infixOp(op, pair.get(0), pair.get(1));
      } else {
        throw new BException("internal error: " + op.name 
        + " has illegal arity " + op.arity);
      }
    } else {
      infixOp(bOp(arg+ZString.MEM+arg), p.getLeftExpr(), p.getRightExpr());
    }
    return p;
  }

  public Term visitFalsePred(FalsePred p)
  {
    out_.print("false");
    return p;
  }

  public Term visitTruePred(TruePred p)
  {
    out_.print("true");
    return p;
  }

  public Term visitExistsPred(ExistsPred p)
  {
    out_.beginPrec(out_.TIGHTEST);
    out_.print("#(");
    ZSchText stext = p.getZSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out_.print(").");
    printPred(Create.andPred(typesconds, p.getPred()));
    out_.endPrec(out_.TIGHTEST);
    return p;
  }

  public Term visitForallPred(ForallPred p)
  {
    out_.beginPrec(out_.TIGHTEST);
    out_.print("!(");
    ZSchText stext = p.getZSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out_.print(").");
    printPred(getFactory().createImpliesPred(typesconds, p.getPred()));
    out_.endPrec(out_.TIGHTEST);
    return p;
  }


  //=========================================================
  // Expressions
  //=========================================================

  public Term visitLambdaExpr(LambdaExpr e)
  {
    out_.beginPrec(out_.TIGHTEST);
    out_.print("%");
    ZSchText stext = e.getZSchText();
    Pred types = splitSchText(stext);  // this prints the names
    out_.print(".(");
    printPred(Create.andPred(types, stext.getPred()));
    out_.print(" | ");
    printExpr(e.getExpr());
    out_.print(")");
    out_.endPrec(out_.TIGHTEST);
    return e;
  }

  public Term visitZName(ZName zName)
  {
    String name = zName.accept(new PrintVisitor());
    sLogger.fine("BTermWriter.visitName(" + zName + ") sees " + name);
    if (name.equals(ZString.EMPTYSET))
      out_.print("{}");
    else if (name.equals(ZString.NAT))
      out_.print("NAT");
    else if (name.equals(ZString.NAT + ZString.SE + "1" + ZString.NW))
      out_.print("NAT1");
    else if (name.equals(ZString.NUM))
      out_.print("INT");
    else if (name.equals(ZString.ARITHMOS)) // we only handle ints
      out_.print("INT");
    else
      out_.printName(zName);
    return zName;
  }

  public Term visitNumExpr(NumExpr e)
  {
    out_.print(e.getNumeral().accept(new PrintVisitor()));
    return e;
  }

  public Term visitApplExpr(ApplExpr e)
  {
    // Try to map the function to a B operator.
    BOperator op = null;
    if (e.getLeftExpr() instanceof RefExpr) {
      RefExpr func = (RefExpr)e.getLeftExpr();
      ZName name = func.getZName();
      if (! hasDecorations(name)) {
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
        List<Expr> pair = ((TupleExpr)e.getRightExpr()).getZExprList();
        if (pair.size() != 2) {
          throw new BException("B " + op.name + " applied to "
          + pair.size() + " args.");
        }
        infixOp(op, pair.get(0), pair.get(1));
      } else {
        throw new BException("internal error: " + op.name 
          + " has illegal arity " + op.arity);
      }
    } else {
      // Print:  left(right)
      out_.beginPrec(out_.TIGHTEST);
      e.getLeftExpr().accept(this);
      // beginPrec will add the opening "(".
      out_.beginPrec(out_.LOOSEST);
      e.getRightExpr().accept(this);
      // endPrec will add the closing "(".
      out_.endPrec(out_.LOOSEST);
      out_.endPrec(out_.TIGHTEST);
    }
    return e;
  }

  public Term visitRefExpr(RefExpr e)
  {
    BOperator op = null;
    ZName name = e.getZName();
    if (! hasDecorations(name)) {
      op = bOp(name.getWord());
    }
    sLogger.fine("RefExpr(" + name.getWord() + "...) --> B " + op);
    if (op != null && op.arity == e.getZExprList().size()) {
      if (op.arity == 1) {
        unaryOp(op, e.getZExprList().get(0));
      } else {
        infixOp(op, e.getZExprList().get(0), e.getZExprList().get(1));
      }
    } else {
      name.accept(this);
    }
    return e;
  }

  public Term visitPowerExpr(PowerExpr e)
  {
    BOperator op = bOp(ZString.POWER+arg);
    sLogger.fine("printing PowerExpr.  op=" + op);    
    unaryOp(op, e.getExpr());
    return e;
  }

  public Term visitSetCompExpr(SetCompExpr setCompExpr)
  {
    if (setCompExpr.getExpr() != null) {
      String msg = "SetCompExpr with expr " + setCompExpr.getExpr() +
        " not yest supported";
      throw new UnsupportedOperationException(msg);
    }
    out_.beginPrec(out_.TIGHTEST);
    out_.print("{");
    ZSchText stext = setCompExpr.getZSchText();
    Pred types = splitSchText(stext);  // this prints the names
    Pred typesconds = Create.andPred(types, stext.getPred());
    out_.print(" | ");
    printPred(typesconds);
    out_.print("}");
    out_.endPrec(out_.TIGHTEST);
    return setCompExpr;
  }

  public Term visitSetExpr(SetExpr set)
  {
    out_.beginPrec(out_.TIGHTEST);
    out_.print("{");
    out_.beginPrec();
    out_.beginPrec(COMMA_PREC+1);
    for (Iterator<Expr> i = set.getZExprList().iterator(); i.hasNext(); ) {
      out_.printExpr(i.next());
      if (i.hasNext()) out_.print(", ");
    }
    out_.endPrec(COMMA_PREC+1);
    out_.endPrec();
    out_.print("}");
    out_.endPrec(out_.TIGHTEST);
    return set;
  }

  public Term visitProdExpr(ProdExpr e)
  {
    List<Expr> sets = e.getZExprList();
    if (sets.size() == 2) {
      infixOp(bOp(arg+ZString.CROSS+arg), sets.get(0), sets.get(1));
    }
    else {
      // construct a right associative tree of binary cartesian products
      assert sets.size() > 2;
      int last = sets.size() - 1;
      Expr prod = sets.get(last);
      for ( ; last >= 0; last--)
	prod = getFactory().createProdExpr(sets.get(last), prod);
      visitProdExpr((ProdExpr)prod);
    }
    return e;
  }

  public Term visitTupleExpr(TupleExpr e)
  {
    List<Expr> sets = e.getZExprList();
    if (sets.size() == 2) {
      infixOp(bOp(arg+","+arg), sets.get(0), sets.get(1));
    }
    else {
      // construct a right associative tree of binary cartesian products
      assert sets.size() > 2;
      int last = sets.size() - 1;
      Expr pair = sets.get(last);
      for ( ; last >= 0; last--)
	pair = getFactory().createTupleExpr(sets.get(last), pair);
      visitTupleExpr((TupleExpr)pair);
    }
    return e;
  }

  private boolean hasDecorations(ZName zName)
  {
    StrokeList strokeList = zName.getStrokeList();
    if (strokeList instanceof List) {
      return ((List) strokeList).size() > 0;
    }
    return false;
  }

/*
  // ================ unused  TODO: Add these? =======================
  public Object visitFreetype(Freetype zedObject)
  { 
    return zedObject;
  }

  public Object visitNameNamePair(NameNamePair zedObject)
  {
    return zedObject;
  }

  public Object visitLetExpr(LetExpr zedObject)
  {
    return zedObject;
  }

  public Object visitSignature(Signature zedObject)
  {
    return zedObject;
  }

  public Object visitConstDecl(ConstDecl zedObject)
  {
    return zedObject;
  }

  public Object visitProdType(ProdType zedObject)
  {
    return zedObject;
  }

  public Object visitDecl(Decl zedObject)
  {
    return zedObject;
  }

  public Object visitImpliesExpr(ImpliesExpr zedObject)
  {
    return zedObject;
  }

  public Object visitMuExpr(MuExpr zedObject)
  {
    return zedObject;
  }

  public Object visitSchExpr2(SchExpr2 zedObject)
  {
    return zedObject;
  }

  public Object visitExistsExpr(ExistsExpr zedObject)
  {
    return zedObject;
  }

  public Object visitExists1Expr(Exists1Expr zedObject)
  {
    return zedObject;
  }

  public Object visitForallExpr(ForallExpr zedObject)
  {
    return zedObject;
  }

  public Object visitVarDecl(VarDecl zedObject)
  {
    return zedObject;
  }

  public Object visitFreePara(FreePara zedObject)
  {
    return zedObject;
  }

  public Object visitCompExpr(CompExpr zedObject)
  {
    return zedObject;
  }

  public Object visitBindExpr(BindExpr zedObject)
  {
    return zedObject;
  }

  public Object visitCondExpr(CondExpr zedObject)
  {
    return zedObject;
  }

  public Object visitNameExprPair(NameExprPair zedObject)
  {
    return zedObject;
  }

  public Object visitTupleSelExpr(TupleSelExpr zedObject)
  {
    return zedObject;
  }

  public Object visitLambdaExpr(LambdaExpr zedObject)
  {
    return zedObject;
  }

  public Object visitIffExpr(IffExpr zedObject)
  {
    return zedObject;
  }

  public Object visitQntExpr(QntExpr zedObject)
  {
    return zedObject;
  }

  public Object visitUnparsedZSect(UnparsedZSect zedObject)
  {
    return zedObject;
  }

  public Object visitUnparsedPara(UnparsedPara zedObject)
  {
    return zedObject;
  }

  public Object visitNameTypePair(NameTypePair zedObject)
  {
    return zedObject;
  }

  public Object visitSchText(SchText zedObject)
  {
    return zedObject;
  }

  public Object visitQnt1Expr(Qnt1Expr zedObject)
  {
    return zedObject;
  }

  public Object visitOperand(Operand zedObject)
  {
    return zedObject;
  }

  public Object visitProjExpr(ProjExpr zedObject)
  {
    return zedObject;
  }

  public Object visitBranch(Branch zedObject)
  {
    return zedObject;
  }

  public Object visitGenType(GenType zedObject)
  {
    return zedObject;
  }

  public Object visitPara(Para zedObject)
  {
    return zedObject;
  }

  public Object visitOptempPara(OptempPara zedObject)
  {
    return zedObject;
  }

  public Object visitNameSectTypeTriple(NameSectTypeTriple zedObject)
  {
    return zedObject;
  }

  public Object visitExpr1(Expr1 zedObject)
  {
    return zedObject;
  }

  public Object visitPreExpr(PreExpr zedObject)
  {
    return zedObject;
  }

  public Object visitExprPred(ExprPred zedObject)
  {
    return zedObject;
  }

  public Object visitGivenType(GivenType zedObject)
  {
    return zedObject;
  }

  public Object visitInclDecl(InclDecl zedObject)
  {
    return zedObject;
  }

  public Object visitPred(Pred zedObject)
  {
    return zedObject;
  }

  public Object visitSchemaType(SchemaType zedObject)
  {
    return zedObject;
  }

  public Object visitBindSelExpr(BindSelExpr zedObject)
  {
    return zedObject;
  }

  public Object visitName(Name zedObject)
  {
    return zedObject;
  }

  public Object visitOrExpr(OrExpr zedObject)
  {
    return zedObject;
  }

  public Object visitSpec(Spec zedObject)
  {
    return zedObject;
  }

  public Object visitHideExpr(HideExpr zedObject)
  {
    return zedObject;
  }

  public Object visitGivenPara(GivenPara zedObject)
  {
    return zedObject;
  }

  public Object visitPowerType(PowerType zedObject)
  {
    return zedObject;
  }

  public Object visitAndExpr(AndExpr zedObject)
  {
    return zedObject;
  }

  public Object visitRenameExpr(RenameExpr zedObject)
  {
    return zedObject;
  }

  public Object visitConjPara(ConjPara zedObject)
  {
    return zedObject;
  }

  public Object visitThetaExpr(ThetaExpr zedObject)
  {
    return zedObject;
  }

  public Object visitSetExpr(SetExpr zedObject)
  {
    return zedObject;
  }

  public Object visitSetCompExpr(SetCompExpr zedObject)
  {
    return zedObject;
  }

  public Object visitPipeExpr(PipeExpr zedObject)
  {
    return zedObject;
  }

  public Object visitNegExpr(NegExpr zedObject)
  {
    return zedObject;
  }

  public Object visitDecorExpr(DecorExpr zedObject)
  {
    return zedObject;
  }

  public Object visitParent(Parent zedObject)
  {
    return zedObject;
  }

  public Object visitExists1Pred(Exists1Pred zedObject)
  {
    return zedObject;
  }

  public Object visitSchExpr(SchExpr zedObject)
  {
    return zedObject;
  }
*/
}
