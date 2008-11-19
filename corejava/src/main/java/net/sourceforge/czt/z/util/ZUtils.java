/*
  Copyright (C) 2005, 2006, 2007 Mark Utting
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

package net.sourceforge.czt.z.util;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.TermImpl;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

public final class ZUtils
{
  public static final Factory FACTORY = new Factory();

  /**
   * Do not create instances of this class.
   */
  private ZUtils()
  {
  }

  /**
   * Computes a list of all the NameTypePairs from the given signature
   * whose name ends with the given decoration.  If <code>decor</code>
   * is <code>null</code> a list of all undecored names with its
   * corresponding types is returned.
   */
  public static List<NameTypePair> subsignature(Signature sig,
                                                Class<?> decor)
  {
    List<NameTypePair> result = new ArrayList<NameTypePair>();
    for (NameTypePair pair : sig.getNameTypePair()) {
      final ZName zName = pair.getZName();
      final ZStrokeList strokeList = zName.getZStrokeList();
      final int size = strokeList.size();
      if ((size == 0 && decor == null) ||
          (size > 0 && decor != null &&
           decor.isInstance(strokeList.get(strokeList.size() - 1)))) {
        result.add(pair);
      }
    }
    return result;
  }

  public static boolean isAnonymous(ZSect zSect)
  {
    final String name = zSect.getName();
    final List<Parent> parents = zSect.getParent();
    return Section.ANONYMOUS.getName().equals(name) &&
      parents.size() == 1 &&
      Section.STANDARD_TOOLKIT.getName().equals(parents.get(0).getWord());
  }

  /** 
   * Returns true if the given term is either a boxed or unboxed Z paragraph.
   * That is, a given set, a free type, an axiomatic/generic description,
   * a schema, a horizontal definition, a conjecture, or an operator template.
   */
  public static boolean isZPara(Term term) {
    return
      (term instanceof GivenPara) ||
      (term instanceof FreePara) ||
      (term instanceof AxPara) ||
      (term instanceof ConjPara) ||
      (term instanceof OptempPara);
  }

  /** Schema or generic schema definition (vertical).
   *      AxPara.Box          = SchBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = ConstDecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = SchemaName
   *      ConstDecl.expr      = SchExpr
   *
   * Axiomatic or generic definitions
   *      AxPara.Box          = AxBox
   *      AxPara.decl         = generics
   *
   *      AxPara.SchText.decl = declared variables
   *      AxPara.SchText.pred = axiomatic predicate
   *
   * Horizontal definition
   *      AxPara.Box          = OmitBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = Constdecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = HorizDefName (either SchName or AbbrvName)
   *      ConstDecl.expr      = HorizDefExpr (either SchExpr or Other)
   */
  
  /** Checks whether the given term is an AxPara */
  public static boolean isAxPara(Term term)
  {
    return term instanceof AxPara;
  }
  
  private static boolean coreBoxedAxiomaticDef(Term term)
  {
    return (isAxPara(term) && ((AxPara) term).getBox().equals(Box.AxBox));
  }
  
  /**
   * Returns the generic formals as NameList of a given term if it is
   * AxPara or null otherwise.  This is valid for any kind of
   * AxPara. That is, it returns the generic parameters for generic
   * boxes, horizontal definitions, and schemas.
   */
  public static NameList getAxParaGenFormals(Term term)
  {
    return (isAxPara(term) ? ((AxPara) term).getNameList() : null);
  }

  /**
   * Returns the generic formals as ZNameList of a given term if it is
   * AxPara or null otherwise This is valid for any kind of
   * AxPara. That is, it returns the generic parameters for generic
   * boxes, horizontal definitions, and schemas.
   */
  public static ZNameList getAxParaZGenFormals(Term term)
  {
    return term == null ? null : assertZNameList(getAxParaGenFormals(term));
  }

  /**
   * Returns the ZDeclList of axiomatic or generic definitions, or
   * null if term is not an AxPara with AxBox.
   */
  public static ZDeclList getAxBoxDecls(Term term)
  {
    ZDeclList result = null;
    if (coreBoxedAxiomaticDef(term)) {          
      return ((AxPara) term).getZSchText().getZDeclList();
    }
    return result;
  }

  /**
   * Returns the Pred of axiomatic or generic definitions, or null if
   * term is not an AxPara with AxBox.
   */
  public static Pred getAxBoxPred(Term term)
  {
    Pred result = null;
    if (coreBoxedAxiomaticDef(term)) {          
      return ((AxPara) term).getZSchText().getPred();
    }
    return result;
  }

  /**
   * Return the generic formals of a given term if it is AxPara or
   * null otherwise
   */
  public static boolean isBoxedAxiomaticDef(Term term)
  {
    boolean result = coreBoxedAxiomaticDef(term);
    if (result) {
      NameList nl = getAxParaGenFormals(term);      
      result = (nl == null ||
                ((nl instanceof ZNameList) && ((ZNameList) nl).isEmpty()));
    }
    return result;
  }

  /**
   * Checks whether the given term is an AxPara with AxBox (i.e. it
   * comes from a \begin{gendef}[...]/GENAX
   */
  public static boolean isBoxedGenericDef(Term term)
  {
    boolean result = coreBoxedAxiomaticDef(term);
    if (result) {
      ZNameList nl = getAxParaZGenFormals(term);      
      result = (nl != null && !nl.isEmpty());
    }
    return result;
  }

  /**
   * Checks whether the given term is an AxPara with OmixBox.
   */
  public static boolean isHorizontalDef(Term term)
  {
    return (isAxPara(term) && ((AxPara) term).getBox().equals(Box.OmitBox));
  }

  /**
   * Checks whether the given term <code>isHorizontalDef(Term)</code>
   * and <code>isSchema(Term)</code>
   */
  public static boolean isHorizontalSchema(Term term)
  {
    return (isHorizontalDef(term) && isSchema(term));
  }

  /**
   * Checks whether the given term <code>isHorizontalDef(Term)</code>
   * and <code>!isSchema(Term)</code>
   */
  public static boolean isAbbreviation(Term term)
  {
    return (isHorizontalDef(term) && !isSchema(term));
  }

  /**
   * Returns true if the AxPara has been properly encoded as either a
   * schema box or a horizontal definition. It is useful for
   * assertions.
   */
  public static boolean isAxParaSchemaOrHorizDefValid(AxPara axp)
  {
    // ensure our understanding of the CZT encoding is right.
    return (axp.getZSchText().getPred() == null) &&
           (axp.getZSchText().getZDeclList().size() == 1) &&
           (axp.getZSchText().getZDeclList().get(0) instanceof ConstDecl);
  }

  /**
   * Checks whether the given paragraph is an <code>AxPara</code> term
   * encoded as a schema or not. That is, it checks whether the term
   * is properly encoded as either a horizontal or a boxed schema.
   */
  public static boolean isSchema(Term term) 
  {
    boolean result = isAxPara(term);
    if (result) {
      AxPara axp = (AxPara) term;
      result = axp.getBox().equals(Box.SchBox);        
      // If it is not a SchBox then check for OmitBox.    
      if (!result) {
        result = axp.getBox().equals(Box.OmitBox);
        // If it is an OmitBox, check if it is a schema or not.
        if (result) {
          assert isAxParaSchemaOrHorizDefValid(axp);
          ConstDecl cdecl = (ConstDecl)axp.getZSchText().getZDeclList().get(0);
          result = (cdecl.getExpr() instanceof SchExpr);
        }
        // Otherwise, it is an AxBox and not a schema, result = false already.
      }
      // Otherwise, it is already a schema.
    }
    // Otherwise, it is not an AxPara, so not a schema.
    return result;
  }

  /**
   * If the given paragraph <code>isSchema(para)</code>, returns the
   * declared schema name. Otherwise, the method returns null.
   */
  public static Name getSchemaName(Term term)
  {
    Name result = null;
    if (isSchema(term) || isHorizontalDef(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getName();
    }
    return result;
  } 

  public static Expr getSchemaDefExpr(Term term)  
  {
    Expr result = null;
    if (isSchema(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getExpr();
    }
    return result;
  }

  public static ZNameList getSchemaZGenFormals(Term term)
  {
    ZNameList result = null;
    if (isSchema(term)) {
      return getAxParaZGenFormals(term);
    }
    return result;
  }

  public static Name getAbbreviationName(Term term)  
  {
    Name result = null;
    if (isAbbreviation(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getName();
    }
    return result;
  }

  public static Expr getAbbreviationExpr(Term term)  
  {
    Expr result = null;
    if (isAbbreviation(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getExpr();
    }
    return result;
  }

  public static ZNameList getAbbreviationZGenFormals(Term term)
  {
    ZNameList result = null;
    if (isAbbreviation(term)) {
      return getAxParaZGenFormals(term);
    }
    return result;
  }

  /**
   * Returns whether the given expression is an empty set as a reference to
   * <code>ZString.EMPTYSET<code>.
   */
  public static boolean isEmptySetRefExpr(Object a) 
  {      
    boolean result = (a instanceof RefExpr);        
    if (result) 
    {
      RefExpr r = (RefExpr)a;
      // false mixfix, as the result of createGenInst(...)
      result = r.getMixfix() != null && !r.getMixfix();
      if (result) 
      {
        result = r.getZName().getWord().equals(ZString.EMPTYSET);
      }
    }      
    return result;
  }

  
  public static boolean isRefExpr(Term term)
  {
    return term instanceof RefExpr;
  }

  public static boolean isApplExpr(Term term)
  {
    return term instanceof ApplExpr;
  }

  public static boolean isSetExpr(Term term)
  {
    return term instanceof SetExpr;
  }

  public static boolean isTupleExpr(Term term)
  {
    return term instanceof TupleExpr;
  }

  public static boolean isMemPred(Term term)
  {
    return term instanceof MemPred;
  }

  public static boolean isAndPred(Term term)
  {
    return term instanceof AndPred;
  }

  /**
   * Returns true if term is a reference expression. That is, a
   * RefExpr with mixfix and explicit false, and the list of
   * instantiating expressions is empty. For example: \arithmos, \num,
   * \emptyset.  For \emptyset, the typechecker transforms it to a
   * generic application and explicit remains false (see 13.2.3.3)
   * (i.e. isReferenceExpr(\emptyset) after typechecking might be
   * false if generic actuals are given, as in \emptyset[\nat]).
   */  
  public static boolean isReferenceExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isRefExpr(term);
    if (result) {
      RefExpr r = (RefExpr) term;
      result = (!r.getMixfix() && !r.getExplicit() &&
                r.getZExprList().isEmpty());
    }
    return result;
  }

  /**
   * Returns true if term is a generic operator instantiation. That
   * is, a RefExpr with mixfix false and the list of instantiating
   * expressions is non-empty (it contains [T]). The explicit
   * attribute indicates whether the instantiating expressions are
   * explicitly given in the specification (explicit is true) or
   * whether they were inferred by the typechecker (explicit is
   * false). For example: \emptyset[T] or \emptyset.
   */
  public static boolean isGenInstExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isRefExpr(term);
    if (result) {
      RefExpr r = (RefExpr) term;
      result = (!r.getMixfix() && !r.getZExprList().isEmpty());
    }
    return result;
  }

  /**
   * Another less common example would be (\_ \fun \_)[S, T].
   * In this case,
   * RefExpr(ZName("_->_"), ZExprList(
   *    RefExpr(ZName("S"), MF=F, EX=F),
   *    RefExpr(ZName("T"), MF=F, EX=F)),
   *    MF=F, EX=T)
   */
  public static boolean isExplicitGenInstExpr(Term term)
  {
    return isGenInstExpr(term) && ((RefExpr) term).getExplicit();
  }

  /**
   * Returns true if term is Generic Operator Application. That is, a
   * RefExpr with mixfix and explicit true, and the list of
   * instantiating expressions is non-empty (it contains [S,T]). For
   * example: S \fun T.
   */
  public static boolean isGenOpApplExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isRefExpr(term);
    if (result) {
      RefExpr r = (RefExpr) term;
      result = (r.getMixfix() && r.getExplicit() && 
                !r.getZExprList().isEmpty());
    }
    return result;
  }

  /**
   * Returns true whenever the given RefExpr is valid (i.e. either
   * Reference, Generic Operator application, or Generic
   * Instantiation).  It should never be false for expressions created
   * by the parser.  This is useful for assertion whenever RefExpr are
   * created on-the-fly.
   */
  public static boolean isRefExprValid(RefExpr term)
  {
    return
      isReferenceExpr(term) || isGenInstExpr(term) || isGenOpApplExpr(term);
  }

  /**
   * Returns the list of instantiating expressions in Generic Operator
   * Application RefExpr or null if it isn't one. That is, it returns
   * [S,T] from "S \fun T".  Not that it will return null if term is
   * "(\_ \fun \_)[S, T]"
   */
  public static ZExprList getGenOpApplZGenActuals(Term term)
  {
    ZExprList result = null;
    if (isGenOpApplExpr(term)) {
      result = ((RefExpr) term).getZExprList();
    }
    return result;
  }

  /** 
   * Returns true if term is an function operator application
   * expression.  That is, an term is an ApplExpr with mixfix TRUE,
   * and the first (left) expression as the name (e.g. " _ + _ ")
   * (that is, a RefExpr) has mixfix FALSE, and the second (right)
   * expression is (S,T).  For example: "(S + T)".  There is no case
   * of ApplExpr where RefExpr mixfix is true.  For instance, both "A
   * (\_ \fun\_)[S, T] B" and "(\_ \fun\_)[S, T] (A, B)" parse with
   * ApplExpr and RefExpr mixfix false.
   */  
  public static boolean isFcnOpApplExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isApplExpr(term);
    if (result) {
      ApplExpr appl = (ApplExpr) term;
      result = (appl.getMixfix() && 
                isRefExpr(appl.getLeftExpr()) &&
                ! ((RefExpr) appl.getLeftExpr()).getMixfix());
    }
    return result;
  }

  /** 
   * Returns true if term is an application expression. That is, an
   * term is an ApplExpr with mixfix FALSE, the first (left)
   * expression is the function name (e.g., \dom), (a RefExpr with
   * mixfix FALSE) and the second (right) expression is the
   * argument. For example: \dom~R or \id~R.  Note that this also
   * covers the case where function operator application is given
   * explicitly, as in "(_+_)(S,T)".
   */ 
  public static boolean isApplicationExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isApplExpr(term);
    if (result) {
      ApplExpr appl = (ApplExpr) term;
      result = (!appl.getMixfix() && 
                isRefExpr(appl.getLeftExpr()) &&
                ! ((RefExpr) appl.getLeftExpr()).getMixfix());
    }
    return result;
  }

  /**
   * Returns true whenever the given ApplExpr is valid (i.e. either
   * function operator application ---implicitly or explicitly---, or
   * application).  It should never be false for expressions created
   * by the parser.  This is useful for assertion whenever ApplExpr
   * are created on-the-fly.
   */
  public static boolean isApplicationExprValid(ApplExpr term)
  {
    return isFcnOpApplExpr(term) || isApplicationExpr(term);
  }

  /**
   * Returns the ApplExpr name for the given term if it is a valid
   * ApplExpr (i.e. isApplicationExprValid), or null otherwise. The
   * name is the first (left) expression of the ApplExpr as a RefExpr,
   * and can be either a function operator application, or just
   * application expression.
   */
  public static RefExpr getApplExprName(Term term)
  {
    RefExpr result = null;
    if (isApplExpr(term) && isApplicationExprValid((ApplExpr) term)) {
      result = (RefExpr) ((ApplExpr) term).getLeftExpr();
    }
    return result;
  }

  /**
   * Returns the ApplExpr arguments for the given term if it is a
   * valid ApplExpr (i.e. isApplicationExprValid), or null
   * otherwise. The arguments are the second (right) expression of the
   * ApplExpr as a ZExprList.  If there are more than one argument
   * (i.e. ApplExpr with TupleExpr as right expr) the list is greater
   * then one.
   */
  public static ZExprList getApplExprArguments(Term term)
  {
    ZExprList result = null;
    if (isApplExpr(term) && isApplicationExprValid((ApplExpr) term)) {
      result = FACTORY.createZExprList();
      Expr arg = ((ApplExpr) term).getRightExpr();
      if (isTupleExpr(arg)) {
        result.addAll(((TupleExpr) arg).getZExprList());
      }
      else {
        result.add(arg);
      }
    }
    return result;
  }

  public static int applExprArity(ApplExpr term)
  {
    ZExprList result = getApplExprArguments(term);
    assert result != null : "Invalid ApplExpr term " + term + 
      ". ApplExpr must always have at least one parameter.";      
    return result.size();
  }

  /**
   * Returns true if term is MemPred with Mixfix=true and the second
   * (right) expression is a singleton set containing the right-hand
   * side of the equality.  For example: "n = m" has left="n" and
   * right="{m}".
   */
  public static boolean isEqualityPred(Term term)
  {
    boolean result = isMemPred(term);
    if (result) {
      MemPred mp = (MemPred) term;
      result = (mp.getMixfix() && isSetExpr(mp.getRightExpr()) &&
                ((SetExpr) mp.getRightExpr()).getZExprList().size() == 1);
    }
    return result;
  }

  /**
   * Returns true if term is MemPred with Mixfix=true, and the second
   * (right) expression is the operator name.  For example, "n < m"
   * has left="(n,m)" and right=" _ < _ ", "disjoint s" has left="s"
   * and right="disjoint _ ", and if foo was declared as a unary
   * postfix operator, then "(2,3) foo" would have left= "(2,3)" and
   * right=" _ foo".
   */
  public static boolean isRelOpApplPred(Term term)
  {
    return (isMemPred(term) && ((MemPred) term).getMixfix() && 
            isRefExpr(((MemPred) term).getRightExpr()));
  }

  /**
   * Returns true if term is MemPred with Mixfix=false, where the
   * first (left) expression is the element, and the second (right)
   * expression is the set.  For example, "n \in S" has left="n" and
   * right="S". Note that this accounts for explicit relational
   * operator application, as in (0, 1) \in (\_ < \_)
   */
  public static boolean isMembershipPred(Term term)
  {
    return isMemPred(term) && ! ((MemPred) term).getMixfix();      
  }

  /**
   * Returns true whenever the given MemPred is valid (i.e. either
   * equality, set membership, or relational operator application).
   * It should never be false for expressions created by the parser.
   * This is useful for assertion whenever MemPred are created
   * on-the-fly.
   */  
  public static boolean isMemPredValid(MemPred term)
  {
    return
      isEqualityPred(term) || isMembershipPred(term) || isRelOpApplPred(term);
  }

  /**
   * Returns the LHS of a MemPred, which is just the same as
   * term.getLeftExpr()
   */
  public static Expr getMemPredLHS(MemPred term)
  {
    return term.getLeftExpr();      
  }

  /** 
   *  Returns the RHS of a MemPred, which is just the same as
   *  term.getReftExpr(), unless term is an equality, in which case it
   *  returns the singleton set element of the RHS expression.  * For
   *  example: "n = m" has left="n" and right="{m}", yet
   *  getMemPredRHS="m"!
   */
  public static Expr getMemPredRHS(MemPred term)
  {
    Expr result = term.getRightExpr();
    if (isEqualityPred(term)) {
      result = ((SetExpr) result).getZExprList().get(0);
    }
    return result;
  }
  
  
  /**
   * Returns the relational operator name for the given term if 
   * it is a relational operator MemPred (i.e. isRelOpApplPred), 
   * or null otherwise. The name is the second (right) expression 
   * of the MemPred term returned as a RefExpr.
   */
  public static RefExpr getRelOpName(Term term) 
  {
    RefExpr result = null;
    if (isRelOpApplPred(term))
    {
      result = (RefExpr)getMemPredRHS((MemPred)term);            
    }
    return result;
  }

  /**
   * Returns the relational operator application arguments, or null if
   * term is not a MemPred relational operator application
   * (i.e. !isRelOpApplPred).  For relational operator application the
   * first (left) expression is usually a tuple containing the
   * corresponding number of arguments.  However, for a unary
   * operator, the left expression does not have to be a tuple.  For
   * example, "n &lt; m" has left="(n,m)", right=" _ &lt; _ ", and arity 2;
   * "disjoint s" has left="s", right="disjoint _ ", and arity 1; and
   * if foo was declared as a unary postfix operator, then "(2,3) foo"
   * would have left= "(2,3)", right=" _ foo", and arity 2.  As no
   * application has empty parameters (i.e. it would be a RefExpr),
   * the result should never be empty (?)
   */
  public static ZExprList getRelOpApplPredLHSArguments(Term term)
  {
    ZExprList result = null;
    if (isRelOpApplPred(term)) {
      result = FACTORY.createZExprList();
      Expr lhs = getMemPredLHS(((MemPred) term));
      if (isTupleExpr(lhs)) {
        result.addAll(((TupleExpr) lhs).getZExprList());
      }
      else {
        result.add(lhs);
      }
      assert ! result.isEmpty() :
        "Relational operator application must have at least one LHS argument";
    }
    return result;
  }

  /**
   * Returns the relational operator application aritity (i.e. its
   * number of parameters), or -1 if term is not a MemPred relational
   * operator application (i.e. !isRelOpApplPred).  For relational
   * operator application the first (left) expression is usually a
   * tuple containing the corresponding number of arguments.  However,
   * for a unary operator, the left expression does not have to be a
   * tuple.  For example, "n &lt; m" has left="(n,m)", right=" _ &lt; _ ",
   * and arity 2; "disjoint s" has left="s", right="disjoint _ ", and
   * arity 1; and if foo was declared as a unary postfix operator,
   * then "(2,3) foo" would have left= "(2,3)", right=" _ foo", and
   * arity 2.  As no application has empty parameters (i.e. it would
   * be a RefExpr), arity should never be 0 ?
   */
  public static int getRelOpApplPredArity(Term term)
  {
      /*
      int result = -1;
      if (isRelOpApplPred(term)) {
          result = 1;
          Expr lhs = getMemPredLHS(((MemPred) term));
          if (isTupleExpr(lhs)) {
              result = ((TupleExpr) lhs).getZExprList().size();
          }
      }
      assert result != 0 : "Relational operator application arity can never be 0";
      return result;       
      */
    ZExprList args = getRelOpApplPredLHSArguments(term);      
    int result = args == null ? -1 : args.size();
    assert result != 0 :
      "Relational operator application arity can never be 0";
    return result;
  }

  /** Returns true if given term is an AndPred with And.Chain */
  public static boolean isChainedConjunction(Term term)
  {
    return isAndPred(term) && ((AndPred) term).getAnd().equals(And.Chain);
  }
  
   /*
   * The ASCII strings produced are designed to be human-readable,
   * so are not necessarily in LaTeX markup.
   */
  public static void unicodeToAscii(String name, StringBuffer result)
  {
    for(int i = 0; i < name.length(); i++) {
      if (Character.isLetterOrDigit(name.codePointAt(i)) ||
          Character.isSpaceChar(name.codePointAt(i)) ||
          name.charAt(i) == '_' || name.charAt(i) == '$') {
        result.append(name.charAt(i));
      }
      else {
        result.append("U+" +
                      Integer.toHexString(name.codePointAt(i)).toUpperCase());
      }
    }
  }
    
  private static PrintVisitor zPrintVisitor_ = new PrintVisitor();
  
  public static String toStringZName(ZName name)
  {
    assert !zPrintVisitor_.getPrintIds() : "by default do not print ids at ZUtils";
    // default is (getPrintUnicode() && !zPrintVisitor_.getPrintIds())
    return zPrintVisitor_.visit(name);
  }
  
  public static String toStringZName(ZName name, boolean printUnicode, boolean printIds)
  {     
    /*
    try 
    {
      assertZPrintVisitor(assertZTermImpl(name).getFactory().getToStringVisitor()).setPrintIds(printIds);      
      assertZPrintVisitor(assertZTermImpl(name).getFactory().getToStringVisitor()).setPrintUnicode(printUnicode);                       
    } catch (UnsupportedAstClassException e)
    {      
      
    } 
    // change flags back  
     */
    
    boolean b1 = zPrintVisitor_.setPrintIds(printIds);
    boolean b2 = zPrintVisitor_.setPrintUnicode(printUnicode);
    String result = zPrintVisitor_.visit(name);
    zPrintVisitor_.setPrintIds(b1);
    zPrintVisitor_.setPrintUnicode(b2);    
    
    return result;
  }

  public static ZBranchList assertZBranchList(Term term)
  {
    if (term instanceof ZBranchList) {
      return (ZBranchList) term;
    }
    final String message =
      "Expected a ZBranchList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZName assertZName(Term term)
  {
    if (term instanceof ZName) {
      return (ZName) term;
    }
    final String message =
      "Expected a ZName but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZNumeral assertZNumeral(Term term)
  {
    if (term instanceof ZNumeral) {
      return (ZNumeral) term;
    }
    final String message =
      "Expected a ZNumeral but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZParaList assertZParaList(Term term)
  {
    if (term instanceof ZParaList) {
      return (ZParaList) term;
    }
    final String message =
      "Expected a ZParaList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZExprList assertZExprList(Term term)
  {
    if (term instanceof ZExprList) {
      return (ZExprList) term;
    }
    final String message =
      "Expected a ZExprList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZNameList assertZNameList(Term term)
  {
    if (term instanceof ZNameList) {
      return (ZNameList) term;
    }
    final String message =
      "Expected a ZNameList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZDeclList assertZDeclList(Term term)
  {
    if (term instanceof ZDeclList) {
      return (ZDeclList) term;
    }
    final String message =
      "Expected a ZDeclList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZFreetypeList assertZFreetypeList(Term term)
  {
    if (term instanceof ZFreetypeList) {
      return (ZFreetypeList) term;
    }
    final String message =
      "Expected a ZFreetypeList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZSchText assertZSchText(Term term)
  {
    if (term instanceof ZSchText) {
      return (ZSchText) term;
    }
    final String message =
      "Expected a ZSchText but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static ZStrokeList assertZStrokeList(Term term)
  {
    if (term instanceof ZStrokeList) {
      return (ZStrokeList) term;
    }
    final String message =
      "Expected a ZStrokeList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  // useful to get access to the getPrintVisitor() method
  public static ZFactoryImpl assertZFactoryImpl(Object factory) {
    if (factory instanceof ZFactoryImpl) {
      return (ZFactoryImpl) factory;
    }
    final String message = "Expected a ZFactoryImpl but found " + 
      String.valueOf(factory);
    throw new UnsupportedAstClassException(message);    
  }
  
  // useful to get access to the z.PrintVisitor class, hence set/getPrintIds()
  public static PrintVisitor assertZPrintVisitor(Object visitor) {
    if (visitor instanceof PrintVisitor) {
      return (PrintVisitor) visitor;
    }
    final String message = "Expected " + PrintVisitor.class.toString() + 
      " but found " + String.valueOf(visitor);
    throw new UnsupportedAstClassException(message);    
  }
  
  public static TermImpl assertZTermImpl(Object term) {
    if (term instanceof TermImpl) {
      return (TermImpl) term;
    }
    final String message = "Expected the default (Z) implementation of Term" +
      " but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);    
  }  
  
  /**
   * Test whether the base name and strokes of two ZNames are equal.
   */
  public static boolean namesEqual(ZName zName1, ZName zName2)
  {
    boolean result = zName1.getWord().equals(zName2.getWord()) &&
      zName1.getStrokeList().equals(zName2.getStrokeList());
    return result;
  }
  
  /**
   * Test whether the base name and strokes of two Names are equal.
   */
  public static boolean namesEqual(Name name1, Name name2)
  {
    boolean result = false;
    if (name1 instanceof ZName && name2 instanceof ZName)
    {
      result = namesEqual((ZName) name1, (ZName) name2);
    }
    return result;
  }
  
  /**
   * Test whether a list contains a ZName.
   * @param list the list to search.
   * @param zName the ZName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsZName(List<ZName> list,
    ZName zName)
  {
    boolean result = false;
    for (ZName next : list)
    {
      if (namesEqual(next, zName))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  /**
   * Test whether a list contains a ZName with the same ID.
   * @param list the list to search.
   * @param zName the ZName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsID(List<ZName> list,
    ZName zName)
  {
    boolean result = false;
    for (ZName next : list)
    {
      if (next.getId().equals(zName.getId()))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  public static boolean idsEqual(String id1, String id2)
  {
    boolean result = id1 != null && id2 != null && id1.equals(id2);
    return result;
  }
  
  /**
   * Sorts the name type pairs within the given signature. Sorting occurs
   * with respect to the compareTo protocol described in this class.
   */
  public static Signature sort(Signature signature)
  {
    sort(signature.getNameTypePair());
    return signature;
  }
  
  /**
   * Sorts the list of name type pairs given. Sorting occurs
   * with respect to the compareTo protocol described in this class.
   */
  public static List<NameTypePair> sort(List<NameTypePair> pairs)
  {
    for (int j = 1; j < pairs.size(); j++)
    {
      NameTypePair pair = pairs.get(j);
      int i = j - 1;
      while (i >= 0 && compareTo(pairs.get(i).getZName(),
        pair.getZName()) > 0)
      {
        pairs.set(i + 1, pairs.get(i));
        i--;
      }
      pairs.set(i + 1, pair);
    }
    return pairs;
  }
  
  public static List<ZName> sortNames(List<ZName> names)
  {
    for (int j = 1; j < names.size(); j++)
    {
      ZName zName = names.get(j);
      int i = j - 1;
      while (i >= 0 && compareTo(names.get(i), zName) > 0)
      {
        names.set(i + 1, names.get(i));
        i--;
      }
      names.set(i + 1, zName);
    }
    return names;
  }
  
  /**
   * Inserts all elements from pairsB in pairsA, provided pairsA are sorted.
   */
  public static void insert(List<NameTypePair> pairsA,
    List<NameTypePair> pairsB)
  {
    for (NameTypePair pair : pairsB)
    {
      insert(pairsA, pair);
    }
  }
  
  /**
   * Inserts all elements from namesB in namesA, provided namesA are sorted.
   */
  public static void insertNames(List<ZName> namesA,
    List<ZName> namesB)
  {
    for (ZName name : namesB)
    {
      insertNames(namesA, name);
    }
  }
  
  //precondition: pairs is sorted
  public static void insert(List<NameTypePair> pairs, NameTypePair pair)
  {
    int i = 0;
    while (i < pairs.size() &&
      compareTo(pairs.get(i).getZName(), pair.getZName()) < 0)
    {
      i++;
    }
    pairs.add(i, pair);
  }
  
  //precondition: names is sorted
  public static void insertNames(List<ZName> names, ZName name)
  {
    int i = 0;
    while (i < names.size() && compareTo(names.get(i), name) < 0)
    {
      i++;
    }
    names.add(i, name);
  }
  
  private static class ZNameComparator implements Comparator<ZName> 
  {    
    ZNameComparator() { }    

    public int compare(ZName n1, ZName n2) 
    {
      int result = compareTo(n1, n2);
      return result;
    }
    
    public boolean equals(Object o) 
    {
      return o != null && o instanceof ZNameComparator;        
    }
  }
  
  public final static Comparator<ZName> ZNAME_COMPARATOR = new ZNameComparator();
  
  public static int compareTo(ZName zName1, ZName zName2)
  {
    String word1 = zName1.getWord();
    String word2 = zName2.getWord();
    int compareWord = word1.compareTo(word2);
    if (compareWord != 0)
    {
      return compareWord;
    }
    else
    {
      ZStrokeList strokes1 = zName1.getZStrokeList();
      ZStrokeList strokes2 = zName2.getZStrokeList();
      int lengthDiff = strokes1.size() - strokes2.size();
      if (lengthDiff != 0)
      {
        return lengthDiff;
      }
      else
      {
        //sort as ? < ! < ' < num
        for (int i = 0; i < strokes1.size(); i++)
        {
          int stroke1Val = getStrokeValue(strokes1.get(i));
          int stroke2Val = getStrokeValue(strokes2.get(i));
          int compareStroke = stroke1Val - stroke2Val;
          if (compareStroke != 0)
          {
            return compareStroke;
          }
        }
        return 0;
      }
    }
  }
  
  public static int getStrokeValue(Stroke stroke)
  {
    int result = -1;
    if (stroke instanceof InStroke)
    {
      result = 0;
    }
    else if (stroke instanceof OutStroke)
    {
      result = 1;
    }
    else if (stroke instanceof NextStroke)
    {
      result = 2;
    }
    else if (stroke instanceof NumStroke)
    {
      result = 3;
    }
    else
    {
      assert false : "Stroke instanceof " + stroke.getClass().getName();
    }
    return result;
  }
}
