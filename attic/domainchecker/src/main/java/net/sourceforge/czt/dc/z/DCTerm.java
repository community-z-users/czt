/**
Copyright 2007, Leo Freitas
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
package net.sourceforge.czt.dc.z;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.DefinitionType;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Expr0N;
import net.sourceforge.czt.z.ast.Expr1;
import net.sourceforge.czt.z.ast.Expr2;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.IffPred;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LetExpr;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.MuExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.Qnt1Expr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.util.ZUtils;

import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BindExprVisitor;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.CondExprVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.Expr0NVisitor;
import net.sourceforge.czt.z.visitor.Expr1Visitor;
import net.sourceforge.czt.z.visitor.Expr2Visitor;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.IffPredVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
import net.sourceforge.czt.z.visitor.LambdaExprVisitor;
import net.sourceforge.czt.z.visitor.LetExprVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.MuExprVisitor;
import net.sourceforge.czt.z.visitor.NegPredVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.OrPredVisitor;
import net.sourceforge.czt.z.visitor.Qnt1ExprVisitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SetCompExprVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZBranchListVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZExprListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.visitor.ZSchTextVisitor;

import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;

/**
 * <p>
 * Top-level domain checking term. It calculates domain check predicates
 * for all Z terms, where those left out have trivial (true) domain checks.
 * The domain check rules added here are inspired / comes from those defined
 * in the Z/EVES theorem prover, which here have been expanded to Standard Z.
 * </p>
 * <p>
 * These predicates ensure that all functions are applied within their domains,
 * and that definite descriptions are indeed uniquely defined. This is important
 * in order to ensure that expressions in Z specifications are well-formed. 
 * That is, since Z operates under a semi-classical logic, predicate terms
 * are inheritenly consistent, yet the expression terms might not be. Domain
 * checks close this gap. They are similar to some of PVS's type checking conditions. 
 * </p>
 * <p>
 * Often, resulting predicates calculated are just a chain of trivial (true) conjunctions.
 * In such cases, we eliminate the predicate by repetitively applying conjunction 
 * unit laws. By design we keep these transformations to a minumum, though. Thus, we 
 * avoid introducing errors/problems as a result of them, yet try to minimise too
 * many spurious domain check results, as experiments showed to appear often
 * (i.e., domain check safe specification will always have a long chain of conjoined
 *        true predicates as their domain checking conditions).
 * </p>
 * @author leo
 */
public class DCTerm extends TrivialDCTerm implements
  // Para visitors
  //ParaVisitor<Pred>,  see Para should use Term
  ConjParaVisitor<Pred>,
  FreeParaVisitor<Pred>,
  ZFreetypeListVisitor<Pred>,
  FreetypeVisitor<Pred>,
  ZBranchListVisitor<Pred>,
  BranchVisitor<Pred>,
  AxParaVisitor<Pred>,
  ZSchTextVisitor<Pred>,
  OptempParaVisitor<Pred>,
  
  //ZParaListVisitor<Pred>, see DomainChecker.visitZSect  
  
  // Declaration visitors 
  ZDeclListVisitor<Pred>,
  VarDeclVisitor<Pred>,
  ConstDeclVisitor<Pred>,
  InclDeclVisitor<Pred>,

  // Expression visitors
  ZExprListVisitor<Pred>,
  Expr2Visitor<Pred>,     // Expr2
  ApplExprVisitor<Pred>,
  Expr1Visitor<Pred>,     // Expr1
  //ThetaExprVisitor<Pred>,
  Expr0NVisitor<Pred>,    // Expr0N
  //QntExprVisitor<Pred>,   // QntExpr  
  Qnt1ExprVisitor<Pred>,  //    Qnt1Expr  
  LambdaExprVisitor<Pred>,//      LambdaExpr
  LetExprVisitor<Pred>,   //      LetExpr
  MuExprVisitor<Pred>,    //    MuExpr
  SetCompExprVisitor<Pred>,//   SetCompExpr
  CondExprVisitor<Pred>,  // CondExpr
  BindExprVisitor<Pred>,  // BindExpr
  RefExprVisitor<Pred>,   // RefExpr
  SchExprVisitor<Pred>,   // SchExpr
  NumExprVisitor<Pred>,   // NumExpr
  //ZNumeralVisitor<Pred>,  

  //Predicate visitors
  //FactVisitor<Pred>,
  AndPredVisitor<Pred>,
  ImpliesPredVisitor<Pred>,
  IffPredVisitor<Pred>,
  OrPredVisitor<Pred>,
  QntPredVisitor<Pred>,  
  NegPredVisitor<Pred>,
  MemPredVisitor<Pred>,
  ExprPredVisitor<Pred>,
  DomainCheckPropertyKeys
{

  /** 
   * We follow Z/EVES' approach and use the appliesTo function for
   * domain checks over unresolved names. This function is defined 
   * under the dc\_toolkit.tex
   */
  private static final String APPLIESTO_NAME_INFIX = ZString.ARG_TOK + "appliesTo" + ZString.ARG_TOK;
  private static final String APPLIESTO_NAME_NOFIX = "appliesToNofix"; // this name is UNICODE, not LaTeX from DC_toolkit!
  private static final String DOM_NAME = "dom";
  
  public static final String[] TOTAL_OPS = { ZString.FUN, ZString.SURJ, ZString.INJ, ZString.BIJ };
  public static final String[] PARTIAL_OPS = { ZString.PFUN, ZString.PSURJ, ZString.PINJ };              
  
  /**
   * Definition table containing declared types of names. This is important
   * to query known names to see weather they are partial functions that
   * require domain check predicates or not.
   */
  private DefinitionTable defTable_;
  
  private boolean infixAppliesTo_;
  private boolean applyPredTransformers_;
  private ZName appliesToOpName_;

  private final ZName domName_;
  private final PrintVisitor printVisitor_;
    
  /**
   * 
   */
  public DCTerm()
  {
    this(new Factory());
  }  
  
  /** Creates a new instance of DCTerm
   * @param factory 
   */
  public DCTerm(Factory factory)
  {
    super(factory);
    defTable_ = null;    
    domName_ = factory_.createZName(DOM_NAME); // not an operator (see relation_toolkit.tex)!
    applyPredTransformers_ = PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT;
    setInfixAppliesTo(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT);
    printVisitor_ = new PrintVisitor(); // defTable uses a PrintVisitor for lookup names.
  }

  private void setInfixAppliesTo(boolean value)
  {
    infixAppliesTo_ = value;
    // is it (f appliesTo x) or (f, x) \in appliesToNoFix?
    appliesToOpName_ = factory_.createZName(infixAppliesTo_ ? APPLIESTO_NAME_INFIX : APPLIESTO_NAME_NOFIX);
  }
  
  /** TOP-LEVEL METHOD */
  
  /**
   * Runs the domain checking algorithm over the given term and definition table.
   * The definition table is important in order to make sure the types of known 
   * names can be properly inspected. For instance, assuming expressions are ground
   * (i.e., just names), the domain check for "x \cup y" will ultimately depend 
   * on \cup being a total function or having the types of x and y within its domain.
   * The definition table should contain such declarated type information. If null
   * is given, then applies$to will always be used.
   * 
   * @param term to domain check
   * @param dt definition lookup table; if null, applies$to will always be used.
   * @param infixAppliesTo
   * @param applyPredTransf
   * @return domain check predicate for given term
   */
  public Pred runDC(Term term, DefinitionTable dt, boolean infixAppliesTo, boolean applyPredTransf)
  {
    assert term != null : "Invalid term for DC";
    setInfixAppliesTo(infixAppliesTo);
    applyPredTransformers_ = applyPredTransf;
    defTable_ = dt; // a null dts means always "applies$to"!
    Pred result = dc(term);
    defTable_ = null;
    setInfixAppliesTo(defaultInfixAppliesTo());
    applyPredTransformers_ = defaultApplyPredTransformers();
    return result;
  }
  
  public Pred runDC(Term term, DefinitionTable dt)
  {
    return runDC(term, dt, defaultInfixAppliesTo(), defaultApplyPredTransformers());
  }
  
  public Pred runDC(Term term)
  {
    return runDC(term, null, defaultInfixAppliesTo(), defaultApplyPredTransformers());
  }
  
  public boolean isAppliesToInfix()
  {
    return infixAppliesTo_;
  }
    
  public boolean isApplyingPredTransformers()
  {
    return applyPredTransformers_;
  }
  
  protected boolean defaultInfixAppliesTo()
  {
    return PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT;
  }
  
  protected boolean defaultApplyPredTransformers()
  {
    return PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT;
  }

  /** AUXILIARY TERM FACTORY METHODS */
      
  /** 
   * Creates a AndPred from the given arguments with And.Wedge (i.e. lhs \land rhs).
   * We apply conjunction zero, unit, and idempotent laws 
   * transforming the resulting conjunction as:
   * <ul>
   *  <li>false \land P \iff false </li>
   *  <li>false \land P \iff false </li>
   *  <li>true \land P \iff P</li>  
   *  <li>P \land true \iff P</li>
   *  <li>P \land P \iff P</li>
   *  <li>P \land \lnot P \iff false </li>
   * </ul>
   * These transformations are useful when chaining various predicates that
   * become spurious when applying the unit-law exhaustively.
   * 
   * @param lhs left hand side predicate
   * @param rhs right hand side predicate
   * @return LHS \land RHS with And.Wedge, unless transformed
   */
  protected Pred andPred(Pred lhs, Pred rhs)
  {
    assert lhs != null && rhs != null : "Invalid AndPred request!";
    Pred result = null;
    if (applyPredTransformers_)
    {
      // P \land false = \false \land P = P
      if (lhs instanceof FalsePred || rhs instanceof FalsePred)
      {
        result = factory_.createFalsePred();
      }
      // true \land RHS = RHS
      if (lhs instanceof TruePred)
      {
        result = rhs;
      }
      // LHS \land true = LHS
      else if (rhs instanceof TruePred)
      {
        result = lhs;
      }       
      // LHS \land LHS = LHS
      else if (lhs.equals(rhs))
      {
        result = lhs;      
      }    
    }    
    if (result == null)
    {
      // Leave contradiction law (P \land \lnot P) out.
      //Pred innerLHS = lhs instanceof NegPred ? ((NegPred)lhs).getPred() : lhs;
      //Pred innerRHS = rhs instanceof NegPred ? ((NegPred)rhs).getPred() : rhs;      
      //if (innerLHS.equals(innerRHS))
      
      result = factory_.createAndPred(lhs, rhs, And.Wedge);
    }
    return result;
  }
  
  /** 
   * Creates a ForAllPred with the given declarations and predicate. 
   * That is, "\forall decl @ pred". We apply the simple zero-law:
   * <ul>
   *  <li>\forall D @ true \iff true </li>
   * </ul>
   * Even if D is false, this is the right transformation as anything implies true.
   * @param decl 
   * @param pred 
   * @return
   */
  protected Pred forAllPred(ZDeclList decl, Pred pred)
  {
    assert decl != null && pred != null : "Invalid ForAllPred request!";        
    // \forall D @ true \iff true (even if D is false!): Don't do it...    
    Pred result = null;
    if (applyPredTransformers_)
    {
      if (pred instanceof TruePred)
      {
        result = truePred();
      }
    }
    if (result == null)
    {
      result = factory_.createForallPred(factory_.createZSchText(decl, null), pred);
    }
    return result;
  }
  
  /** 
   * Creates an ImpliesPred from the given arguments (i.e. p \implies q)
   * We apply implication right-zero, right-unit, false-antecedent,
   * false-consequent, and reflection laws transforming the resulting 
   * conjunction as:
   * <ul>
   *  <li>P \implies true \iff true </li>
   *  <li>true \implies P \iff true </li>
   *  <li>P \implies false \iff \lnot P</li>  
   *  <li>false \implies P \iff true</li>
   *  <li>P \implies P \iff true</li>
   * </ul>
   * @param p 
   * @param q
   * @return 
   */
  protected Pred impliesPred(Pred p, Pred q) 
  {
    assert p != null && q != null : "Invalid ImpliesPred request!";
    Pred result = null;
    if (applyPredTransformers_)
    {
      // true ==> q     <==> q
      // p    ==> true  <==> true (which is q)
      if (p instanceof TruePred || q instanceof TruePred)
      {
        result = q;
      }
      // false ==> q     <==> true
      // P     ==> P     <==> true
      else if ((p instanceof FalsePred) || p.equals(q))
      {
        result = truePred();
      }
      // p     ==> false <==> not p
      else if (q instanceof FalsePred)
      {
        result = factory_.createNegPred(p);
      }
    }
    if (result == null)
    {
      result = factory_.createImpliesPred(p, q);
    }
    return result;
  }
  
  /** Transforms a predicate into a (Sch)Expr (with empty Decl): P --> [ |P] */
  private Expr predSchExpr(Pred pred)
  {
    assert pred != null : "Invalid SchExpr request!";
    return factory_.createSchExpr(factory_.createZSchText(factory_.createZDeclList(), pred));
  }

  /** AUXILIARY COMPOSITIONAL DC METHODS */

  /** Calculates DC for given term (i.e. visits term).
   * @param term
   * @return 
   */
  protected Pred dc(Term term) 
  {
    assert term != null : "Invalid (null) term to domain check!";
    return term.accept(this);
  }
  
  /**
   * Recurses through the list of terms and build an {@link #andPred(net.sourceforge.czt.z.ast.Pred, net.sourceforge.czt.z.ast.Pred)} 
   * for the resuling domain check for each of them. If the list is empty or has one element it is conjoined with "true".
   * That is, for a list &lt;p, q&gt;, it creates "true \land dc(p) \land dc(q)"; whereas an 
   * emptylist just returns "true".
   * 
   * DC(&lt;p, q, ...&gt;) = DC(p) \land DC(q) \land ...
   * @param list
   * @return 
   */
  protected Pred andPredList(List<? extends Term> list)
  {
    assert list != null : "Invalid ListTerm (null)!";
    Pred result = truePred();
    if (!list.isEmpty()) 
    {
      Iterator<? extends Term> it = list.iterator();
      assert it.hasNext();
      Term term = it.next();        
      assert term != null : "Invalid ListTerm member (null)!";
      result = dc(term);
      while (it.hasNext())
      {
        term = it.next();
        result = andPred(result, dc(term));
      }
    }
    return result;
  }
  
  /**
   * Creates a common implied predicate used in some DC calculations
   * for the predicate tree. 
   * 
   * DC(P) \land (P \implies DC(Q))
   * @param p 
   * @param q
   * @return 
   */
  protected Pred impliedPred2DC(Pred p, Pred q) 
  {
    assert p != null && q != null : "Invalid ImpliesPred elements (null)!";
    Pred dcp = dc(p); // DC(P)    
    Pred dcq = dc(q); // DC(Q)    
    return andPred(dcp, impliesPred(p, dcq));
  }
  
  /**
   * Extract schema text predicates. When null (see Z Std syntactic 
   * transformations for when that is the case), just returns true.
   * 
   * @param schText
   * @return
   */
  private Pred getZSchTextPred(ZSchText schText)
  {
    assert schText != null : "Invalid ZSchText (null)!";
    Pred result = schText.getPred();
    // In case of a sch text without Pred, just return true
    if (result == null) 
    {
      result = truePred();
    }
    return result;
  }
  
  /**
   * Creates a common implied predicate (see similar method below), yet 
   * there is a special case (i.e. SetCompExpr), where the the DC(E) is
   * just true (i.e. \{ D | P \} for the usual \{ D | P @ E \}).
   * @param schText
   * @return 
   */
  protected Pred impliedZSchTextDC(ZSchText schText)
  {
    return impliedZSchTextDC(schText, truePred());
  }
  
  /**
   * Creates a common implied predicate used in some DC calculations.
   * That is, given the term "(D | P) @ E", it creates the following
   * DC condition predicate: 
   * 
   * DC(D) \land \forall D @ DC(P) \land (P \implies DC(E))
   *
   * Note that E may also be a predicate, hence we expect a Term
   * @param schText
   * @param term 
   * @return
   */
  protected Pred impliedZSchTextDC(ZSchText schText, Term term) {
    assert schText != null && term != null : "Invalid ZSchText or term (null)!";
    ZDeclList decl = schText.getZDeclList();    
   
    // a schema text might have null pred, in which case
    // that corresponds to [D | true]. So, instead of 
    // returning null, the schText.getPred() returns true
    Pred pred = getZSchTextPred(schText);
    
    Pred dcd = dc(decl); // DC(D)
    Pred dcp = dc(pred); // DC(P)    
    Pred dce = dc(term); // DC(E)
    Pred forAll = forAllPred(decl, andPred(dcp, impliesPred(pred, dce))); // \forall D @ DC(P) \land (P \implies DC(e))
    
    return andPred(dcd, forAll);
  }
  
  /**
   * Checks whether the list of declarations are ConstDecl only. 
   * This is important while checking for LetExpr, and BindExpr 
   * (syntactic/parsing) consistency. 
   * @param decls 
   * @return
   */
  protected boolean isConstDeclOnly(ZDeclList decls)
  {
    boolean result = true;
    Iterator<Decl> it = decls.iterator();
    while (result && it.hasNext()) 
    {
      result = (it.next() instanceof ConstDecl);
    }
    return result;
  }
  
  /**
   * 
   */
  protected enum ApplType { TOTAL, PARTIAL, RELATIONAL };
  
  protected ApplType calculateApplicationType(RefExpr name)
  {
    ApplType result = ApplType.RELATIONAL;    
    if (defTable_ != null) 
    { 
      // attempt retrieving using usual toString?
      DefinitionTable.Definition def = defTable_.lookup(name.getZName().toString());
      
      // if fails, use print visitor - I guess with the embedding of PrintVisiting 
      // within toString this should be just the same anyway...
      if (def == null)
      {
        // following DefinitionTableVisitor implementation, 
        // parse the function name with printVisitor_ for the
        // table lookup definition name.
        String defName = name.getZName().accept(printVisitor_);
        def = defTable_.lookup(defName);
      }      
      
      // If there is a definition for defName
      if (def != null) 
      {
        // If it is a VARDECL with a RefExpr type
        if (//def.getDefinitionKind().equals(DefinitionKind.VARDECL) &&
            def.getExpr() instanceof RefExpr)
        {
          RefExpr refExpr = (RefExpr)def.getExpr();

          // If such declaration is an operator (i.e. _ op _)?
          OperatorName opName = refExpr.getZName().getOperatorName();
          if (opName != null)  
          {
            String opNameWord;
            OperatorName.Fixity fixity = opName.getFixity();
            // if it has fixture, check weather to get first, last or middle argument
            if (!fixity.equals(OperatorName.Fixity.NOFIX))
            {
              String [] names = opName.getWords();
              // if infix / prefix, get the name
              if (names.length > 1 && (opName.isInfix() || opName.isPrefix()))
              {
                opNameWord = names[1];
              }
              else if (names.length > 0 && opName.isPostfix())
              {
                opNameWord = names[0];
              }
              // otherwise, that should be an error? Try the whole name them
              else
              {
                opNameWord = opName.getWord();
              }
            }
            // if it doesn't have fixture, just assume the name itself.
            else
            {
              opNameWord = opName.getWord();
            }
            
            // check all possible options.            
            if (Arrays.asList(TOTAL_OPS).contains(opNameWord))
            {
              result = ApplType.TOTAL;
            }
            else if (Arrays.asList(PARTIAL_OPS).contains(opNameWord))
            {
              result = ApplType.PARTIAL;
            }
          }
          // else, it is not \fun or \pfun, hence use appliesTo
        }
      }
      // else, just use appliesTo
    }
    return result;
  }
  
  /** PARAGRAPHS */

  /**
   * This implements various Z paragraphs:
   * GivenPara  : [N]
   * ConjPara   : \vdash? P
   * UnparsedPara
   * NarrPara
   * LatexMarkupPara: %%Zxxxx xxxx xxxx
   * 
   * as well as the general Para abstract class.
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(Para) \iff true
   *
   * The RHS of this equivalence is the result this method returns.
   * Other unknown paragraphs will be caught by visitTerm, which raises
   * a DomainCheckException.
   */
  //public Pred visitPara(Para term) 
  //{
  //  return truePred();
  //}  
  
  // see DomainChecker.visitZSect! 
  //
  // To keep a reference to the paragraph where certain terms come from,
  // we leave the domain check of ZParaList to be done at the Z Spec top-level
  //
  //Handles a list of paragraphs "P1 ; ...." as "DC(P1) \land ...". */
  //public Pred visitZParaList(ZParaList term)
  //{
  //  return andPredList(term);
  //}

  /**
   * This implements domain check for conjecture paragraphs:
   * ConjPara : [X] "theorem" N \vdash? Pred.
   *
   * Z/EVES does not have DC for ConjPara, and this is missing.
   * We implement it as the domain check of the associated Pred.
   *
   * DC([X] "theorem" N \vdash? Pred) \iff DC(Pred)
   *
   * @param term
   * @return
   */
  @Override
  public Pred visitConjPara(ConjPara term)
  {
    return dc(term.getPred());
  }

  /**
   * This implements various free type paragraphs:
   * FreePara  : N ::= c | b \ldata E \rdata | ... &
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(N ::= c | b \ldata E \rdata) \iff DC(E)
   *
   * The RHS of this equivalence is the result this method returns.
   * As Standard Z allows mutually recursive free types with the "&"
   * keyword, we also handle the free type list, which essentially 
   * is the same as Z/EVES': domain check all constructor's expression E.
   */
  public Pred visitFreePara(FreePara term)
  {
    return dc(term.getFreetypeList());
  }
  
  /** DC a list of Freetype from a FreePara */
  public Pred visitZFreetypeList(ZFreetypeList term)
  {
    return andPredList(term);
  }
  
  /** DC the branch list of each individual Freetype */
  public Pred visitFreetype(Freetype term) 
  {
    return dc(ZUtils.assertZBranchList(term.getBranchList()));
  }
  
  /** DC a list of Branch from a Freetype */
  public Pred visitZBranchList(ZBranchList term)
  {
    return andPredList(term);
  }
  
  /** DC the expression E on a Freetype branch  "b \ldata E \rdata" as "DC(E)". */
  public Pred visitBranch(Branch term)
  {
    // constructors need dc, names don't
    if (term.getExpr() != null)
    {
      return dc(term.getExpr());
    }
    else
    {
      return truePred();
    }
  }
  
  /**
   * This implements various axiomatic description paragraphs:
   * AxPara (from axdef)    : \begin{axdef} D \where P \end{axdef}
   * AxPara (from gendef)   : \begin{gendef}[X] D \where P \end{gendef}
   * AxPara (from schema)   : \begin{schema} D \where P \end{schema}
   * AxPara (from genschema): \begin{schema}[X] D \where P \end{schema}
   * AxPara (from abbrev.)  : \begin{zed} N[X] == E \end{zed}
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\begin{zed} N[X] == E \end{zed})     \iff DC(E)
   * DC(\begin{xxx}[X] D \where P \end{xxx}) \iff DC(D) \land DC(D) \land (\forall D @ DC(P))
   *
   * The RHS of this equivalence is the result this method returns.
   * 
   */
  public Pred visitAxPara(AxPara term)
  {    
    switch (term.getBox()) 
    {
      case AxBox:
        // for AxBox (axdef and gendef), use getAxBoxXXX methods
        ZDeclList decl = ZUtils.getAxBoxDecls(term);
        Pred pred = ZUtils.getAxBoxPred(term);
        
        Pred dcd = dc(decl); // DC(D)
        Pred dcp = dc(pred); // DC(P)

        // DC(D) \land (\forall D @ DC(P))
        return andPred(dcd, forAllPred(decl, dcp));

      case SchBox:
        // for SchBox (schema), use use getSchDefExpr methods
        Expr schExpr = ZUtils.getSchemaDefExpr(term);
        
        // for SchBox, expr must be an SchExpr! Well-formed/parsed ASTs should never suffer from this.
        assert (schExpr instanceof SchExpr) : "Invalid SchBox AxPara, no SchExpr within ConstDecl!";
        
        // for SchBox : DC([ D | P ]) \iff DC(D) \land (\forall D @ DC(P)), which comes from ZSchText DC in SchExpr ;)
        return dc(schExpr);

      case OmitBox:
        // for OmitBox (horiz. def or abbreviations), use getSchemaDefExpr method
        // This can be either a SchExpr (for horizontal definitions) or other abbreviation.        
        
        // If this is a SchExpr...
        Expr horizExpr = ZUtils.getSchemaDefExpr(term);        
        // or else it is an abbreviation
        if (horizExpr == null)
          horizExpr = ZUtils.getAbbreviationExpr(term);
        
        assert horizExpr != null : "Invalid horizontal definition: neither schema construction, nor abbreviation (null)!";
        
        // for OmitBox: DC(n[X] == E) \iff DC(E), where E could be a SchExpr ([ D | P])
        return dc(horizExpr);
        
      default: 
        // this case should never happen, yet we need to return something 
        // in the unlikely case the Java compiler messes up with Box Enums
        // (i.e. corrupted byte code classes)!
        throw new AssertionError("Invalid Box for AxPara! " + term.getBox());
    }
  }
  
  /**
   * Z schema text is part of many productions in the Z grammar.
   * Luckily, all of them share the same DC, which is:
   *
   * DC([ D | P ]) \iff DC(D) \land (\forall D @ DC(P))
   * 
   * The RHS of this equivalence is the result this method returns.
   * 
   */
  public Pred visitZSchText(ZSchText term) 
  {
    ZDeclList decl = term.getZDeclList();
    Pred pred = term.getPred();
    
    //assert pred != null : "Invalid schema text predicate";
    
    Pred dcd = dc(decl); // DC(D)
    
    // case the pred within the given ZSchText is null,
    // which happens in some productions like ConstDecl,
    // just result in "true", which is harmless.
    Pred dcp = (pred != null ? dc(pred) : truePred()); // DC(P)
    
    // DC(D) \land (\forall D @ DC(P))
    return andPred(dcd, forAllPred(decl, dcp));
  }
  
  /** 
   * For operator template paragraphs, we just return true.
   * Z/EVES do not mention this, but they would be the "\syndef"
   * Z/EVES operators. We also check that the precedences are 
   * non-negative (i.e. assert it).
   */
  public Pred visitOptempPara(OptempPara term)
  {
    assert term.getPrec().signum() >= 0 : "Operator template paragraph precedence MUST be non-negative";
    return truePred();
  }
  
  /** DECLARATION TERMS */

  /**
   * This implements DC for a list of declarations
   * D1 ; D2 ...
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(D1 ; D2 ; ....) \iff DC(D1) \land DC(D2) ....
   *
   * The RHS of this equivalence is the result this method returns
   */  
  public Pred visitZDeclList(ZDeclList term)
  {
    return andPredList(term);
  }
  
  /**
   * This implements DC for variable declarations
   * VarDecl: x,...: E
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(x, ....: E) \iff DC(E)
   *
   * The RHS of this equivalence is the result this method returns
   */
  public Pred visitVarDecl(VarDecl term)
  {
    return dc(term.getExpr());
  }
  
  /**
   * This implements DC for constant declarations
   * ConstDecl: n[X,...] == E
   *
   * which in Z/EVES is considered as Standard Z
   * axiomatic definition paragraph with OmitBox
   * (i.e. an horizontal definition or abbreviation).
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(n[X,...] == E) \iff DC(E)
   *
   * The RHS of this equivalence is the result this method returns
   */
  public Pred visitConstDecl(ConstDecl term)
  {
    return dc(term.getExpr());
  }
  
  /**
   * This implements DC for schema inclusion declarations
   * InclDecl: S[E1, ....] or S
   *
   * This covers the Z/EVES domain check rules for:
   *
   * DC(S[E1,...]) \iff DC(E) \land ....
   *
   * The RHS of this equivalence is the result this method returns.
   * All other Decl terms will fall into Term (as false), hence 
   * convering Standard Z declarations only (so far).
   *
   * In Z/EVES this rule is given at the Declarations phrases
   * table, but it should be at the SchExpr, since schema 
   * expressions should also have such checks. In Z/EVES that
   * is fine because they use Spivey's Z, which only allow 
   * RefExpr as IncDecl, rather than any Expr.
   * 
   * For Standard Z in CZT we accept Expr, hence we just
   * forward DC of InclDecl to the expression it represents.
   * In the case where it is a RefExpr, the Z/EVES DC is 
   * implemented. Otherwise, it is just a generalisation 
   * of the Z/EVES rules. 
   */
  public Pred visitInclDecl(InclDecl term)
  {
    return dc(term.getExpr());
  }
  
  /** EXPRESSION TERMS */
  
  public Pred visitZExprList(ZExprList term) 
  {
    return andPredList(term);
  }
  
  /**
   * This implements various binary schema expressions:
   * CompExpr   : S1 \comp S2
   * PipeExpr   : S1 \pipe S2
   * ProjExpr   : S1 \proj S2
   * AndExpr    : S1 \land S2
   * OrExpr     : S1 \land S2
   * ImpliesExpr: S1 \implies S2
   * IffExpr    : S1 \iff S2
   * 
   * as well as the general SchExpr2 abstract class, hence
   * leaving only ApplExpr leaf class to be trated separately
   * within the Expr2 subtree.
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(S1 op S2) \iff DC(S1) \land DC(S2) 
   *
   * The RHS of this equivalence is the result this method returns
   */
  public Pred visitExpr2(Expr2 term)
  {
    return andPred(dc(term.getLeftExpr()), dc(term.getRightExpr()));
  }
  
  /**
   * Application expression is one of the most important cases
   * as it handles function application (potentially) outside
   * their domains, which is the main point of domain checks.
   *
   */
  public Pred visitApplExpr(ApplExpr term) 
  { 
    assert ZUtils.isApplicationExprValid(term) : "Invalid ApplExpr! It is neiter function operator application, nor an application expression.";

    // retrieve f and a, in f~a, or a~f~b, or (_ f _)[X]~a, etc...
    Expr name = ZUtils.getApplExprRef(term);
    ZExprList flatArgs = ZUtils.getApplExprArguments(term); // falttens TupleExpr into a ZExprList
    
    // build basic DC: considers generic instantiation and application arguments
    Pred dcF = dc(name);     // check DC((_F_)) for generic instantiations (MISSING IN Z/EVES!!!)
    Pred dcEList = dc(flatArgs); // check all (_F_) arguments (MISSING IN Z/EVES!!!)   
    Pred basicDC = andPred(dcF, dcEList);
    
    // by default, use f applies$to a, (i.e. defTable_ may be null)
    ApplType applType = name instanceof ApplExpr ? ApplType.RELATIONAL : calculateApplicationType((RefExpr)name);
    Pred applPred;
    Expr packedArgs = term.getRightExpr(); // keeps TupleExpr or just Expr in case of arity of 1    
    switch (applType) 
    {
      case TOTAL:
        applPred = truePred();
        break;
      case PARTIAL:
        // args \in \dom~f
        Expr domF = factory_.createApplication(domName_, name);        
        applPred = factory_.createMemPred(packedArgs, domF, Boolean.FALSE);
        break;
      case RELATIONAL:
        // f applies$to a, which is defined as \_ \appliesTo \_ -> (\exists_1 y: Y @ (a, y) \in f) in dc\_toolkit    
        TupleExpr appliesToArgs = factory_.createTupleExpr(name, packedArgs);
        
        if (isAppliesToInfix())
        {        
          // this format is like f \appliesTo args (i.e. infix operator template)
          applPred = factory_.createRelOpAppl(appliesToArgs, appliesToOpName_); // as an operator
        }
        else
        {
          // Create the appliesTo name exlression 
          Expr appliesToRefExpr = factory_.createRefExpr(appliesToOpName_);
          // this format is like (f, args) \in \appliesTo (i.e. membership predicate)
          applPred = factory_.createMemPred(appliesToArgs, appliesToRefExpr, Boolean.FALSE);
        }
        break;
      default:
        throw new AssertionError("Invalid ApplType Enum (only happens if JVM failure or corrupted byte code.");
    }
    assert applPred != null;        
    return andPred(basicDC, applPred);
  }
  
  /**
   * This implements various unary schema expressions:
   * NegExpr    : \lnot S
   * PreExpr    : \pre S
   * RenameExpr : S[new/old]
   * DecorExpr  : S~'
   * BindSelExpr: S.x
   * HideExpr   : S \ (x,...)
   * 
   * as well as the general expressions:
   * PowerExpr   : \power X
   * TupleSelExpr: (x, y).1
   *
   * leaving only ThetaExpr leaf class to be trated 
   * separately within the Expr1 subtree.
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(op S) \iff DC(S) 
   *
   * The RHS of this equivalence is the result this method returns
   */
  public Pred visitExpr1(Expr1 term)
  {
    return dc(term.getExpr());
  }

  /**
   * This implements various expression list productions:
   * SetExpr    : \{ x, y \}
   * TupleExpr  : (x, y)
   * ProdExpr   : X \cross Y
   *
   * as well as the Expr2N abstract class.
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(E1 op E2 ...) \iff DC(E1) \land DC(E2) ...
   *
   * The RHS of this equivalence is the result this method returns
   */
  public Pred visitExpr0N(Expr0N term) 
  {    
    return dc(term.getZExprList());
  }
  
  /**
   * This implements various quantified schema expression productions:
   * ExistsExpr : \exists   D | P @ SE, where SE could also be a schema
   * Exists1Expr: \exists_1 D | P @ SE, where SE could also be a schema
   * ForallExpr : \forall   D | P @ SE, where SE could also be a schema
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(qnt D | P @ SE) \iff DC(D) \land (\forall D @ DC(P)) \land DC(SE)
   *
   * The RHS of this equivalence is the result this method returns.
   *
   * The Z/EVES reference manual (Section 3.7.1, p.23) states that
   * this DC for such schema quantifications is a weaker version 
   * which does not rely on P to prove DC(SE). Other similar quantified 
   * rules, such as those for predicates and other expressions, do rely
   * on such implication from P, though (see below).
   *
   */
  public Pred visitQnt1Expr(Qnt1Expr term) 
  {
    // DC(D) \land (\forall D @ DC(P)), for [ D | P ]
    Pred dcschtext = dc(term.getZSchText());
    
    Expr expr = term.getExpr();    
    Pred dce = dc(expr); // DC(E)
    
    // DC(D) \land (\forall D @ DC(P)) \land DC(E)
    return andPred(dcschtext, dce);
  }

  /**
   * This implements quantified expression productions, which
   * turns out to be just SetCompExpr (and abstract class QntExpr),
   * since the other element, MuExpr, is dealt with separately.
   * SetCompExpr: \{ D | P @ E }
   *
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\{ D | P @ E \}) \iff DC(D) \land (\forall D @ DC(P) \land (P \implies DC(E)))
   *
   * The RHS of this equivalence is the result this method returns.
   * 
   * Because all other QntExpr are dealt with separately either 
   * in Qnt1Expr, LambdaExpr, or MuExpr.
   */
  //public Pred visitQntExpr(QntExpr term) 
  //{
  //  return impliedZSchTextDC(term.getZSchText(), term.getExpr());
  //}
  
  // Make a clear distinction here for SetCompExpr with default E
  // because we don't want to call dc(null) when E is default (null).
  public Pred visitSetCompExpr(SetCompExpr term)
  {
    if (term.getExpr() == null) // \{ D | P \}
      return impliedZSchTextDC(term.getZSchText());
    else
      return impliedZSchTextDC(term.getZSchText(), term.getExpr());
  }
 
  /**
   * The production for lambda expressions is as follows:
   * LambdaExpr : \lambda  D | P @ E
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\lambda  D | P @ E) \iff DC(D) \land (\forall D @ DC(P) \land (P \implies DC(E)))
   *
   * The RHS of this equivalence is the result this method returns.
   * Note that differently from the other quantified schema expression  
   * rules, here Z/EVES prefers the stronger rule which requires P 
   * implying DC(E) (see Z/EVES reference manual p.23, Section 3.7.1).
   * This is much like the rule for QntExpr.
   *
   * Although LambdaExpr and SetCompExpr have the same domain check,
   * unfortunately we must implement them both. That is because LambdaExpr
   * derives from Qnt1Expr&lt;-QntExpr, whereas SetCompExpr derives from QntExpr
   * directly. So if not explicitly given, LambdaExpr would fall in Qnt1Expr
   * rather than the more general QntExpr.
   */
  public Pred visitLambdaExpr(LambdaExpr term) 
  {
    assert term.getExpr() != null : "Invalid LambdaExpr getExpr() term (null)!";
    return impliedZSchTextDC(term.getZSchText(), term.getExpr());
  }
  
    /**
   * The production for let expressions is as follows:
   * LetExpr : \LET x == E1; .... @ E
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\LET x == E1; .... @ E) \iff DC(E1) ... \land (\LET x == E1; .... @ DC(E))
   *
   * The RHS of this equivalence is the result this method returns.
   *
   * This rule is similar to those for Expr0N as it adds DC for EN in the
   * LET declaration, but it also adds a final DC check for the main E 
   * provided each EN is available. 
   *
   * Nevertheless, in Standard Z a LetExpr shares commonality with
   * QntExpr, rather than Expr0N. Also note that in standard Z let 
   * expressions are just mu expressions (see Standard Z p.136, C.6.7.2).
   * In Standard Z, a LetExpr is a QntExpr, which means the declarations
   * are a list of ConstDecl only, something guaranteed by the parser.
   *
   * Note that the \LET expression in RHS must be transformed into a 
   * Predicate. This is done via the ExprPred production, which is
   * not present in Z/EVES. As ExprPred should not be further analysed
   * for DC, we implement it as itself (i.e. DC(ExprPred) = ExprPred).   
   * Nevertheless, Standard Z does not allow LetPred! So we need to
   * transform DC(E) into an expression as in [ | DC(E)]. In Z/EVES
   * this is not necessary because a predicate is an expression already.
   * This double transformation (i.e. DC(E) into and expression and
   * the LET into a predicate) is unfortunate, yet unavoidable. 
   * 
   * TODO: Decide on this!
   * As in Z/EVES a LetExpr is implicitly implemented, we thought to
   * give the rule as they suggest, rather than reuse the one for MuExpr. 
   * The reason is that the DC for let expression is simpler than the 
   * one for MuExpr. By using MuExpr for Standard Z we could avoid the
   * double transformation mentioned above.
   *
   */
  public Pred visitLetExpr(LetExpr term) 
  {
    // Check for the expressions within the list of declaration
    ZDeclList constdecl = term.getZSchText().getZDeclList();
    
    assert isConstDeclOnly(constdecl) : "Parsing must only allow ConstDecl within the LetExpr ZDeclList!";   
    assert term.getZSchText().getPred() == null : "Parsing must set SchText.Pred on LetExpr to null!"; 
    
    Pred dcd = dc(constdecl);     // DC(D)
    Pred dce = dc(term.getExpr());// DC(E)
    
    // (\LET x == E1, ... @ DC(E)), as an expression to be transformed in a predicate
    LetExpr letexpr = factory_.createLetExpr(term.getZSchText(), predSchExpr(dce));
    Pred letpred = factory_.createExprPred(letexpr);
    
    // DC(D) \land (\LET x == E1, ... @ DC(E))
    return andPred(dcd, letpred);
  }
  
  /**
   * The production for mu expressions is as follows:
   * MuExpr : \mu D | P @ E
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\mu D | P @ E) \iff DC(D) \land (\forall D @ DC(P) \land (P \implies DC(E))) \land (\exists_1 D @ P)
   *
   * The RHS of this equivalence is the result this method returns.
   * Note that differently from the other quantified schema expression  
   * rules, here Z/EVES prefers the stronger rule which requires P 
   * implying DC(E) (see Z/EVES reference manual p.23, Section 3.7.1).
   * This is much like the rule for QntExpr.
   *
   * As in ApplExpr checking for function application consistency,
   * MuExpr is also a fundamental rule in giving meaning to uniqueness 
   * among set containment and equality. This adds to the general 
   * quantified rule the unique existential quantification above.
   *
   */
  public Pred visitMuExpr(MuExpr term) 
  { 
    ZDeclList decl = term.getZSchText().getZDeclList();
    // Pred for Mu could NOT be null!
    assert term.getZSchText().getPred() != null : "Invalid MuExpr: getPred() is null!";
    Pred pred = term.getZSchText().getPred();
    
    // \exists_1 D | true @ P
    Pred exists1 = factory_.createExists1Pred(factory_.createZSchText(decl, truePred()), pred);
    
    // DC(D) \land (\forall D @ DC(P) \land (P \implies DC(E))) \land (\exists_1 D | true @ P)
    return andPred(impliedZSchTextDC(term.getZSchText(), term.getExpr()), exists1);
  }

  
  /**
   * The production for conditional schema expressions is as follows:
   * CondExpr : \IF P \THEN E1 \ELSE E2
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\IF P \THEN E1 \ELSE E2) \iff DC(P) \land (\IF P \THEN DC(E1) \ELSE DC(E2))
   *
   * The RHS of this equivalence is the result this method returns.
   * The same issue that happened in \LET about \IF being an expression
   * that needs to become a predicate is dealt with here.
   *
   */
  public Pred visitCondExpr(CondExpr term) 
  {
    Pred pred = term.getPred();
    Expr expr1 = term.getLeftExpr();
    Expr expr2 = term.getRightExpr();
    
    Pred dcp = dc(pred);   // DC(P)
    Pred dce1 = dc(expr1); // DC(E1)
    Pred dce2 = dc(expr2); // DC(E2);
    
    // (\IF P \THEN DC(E1) \ELSE DC(E2)), as a schema expression
    Expr condExpr = factory_.createCondExpr(pred, predSchExpr(dce1), predSchExpr(dce2));    
    Pred ifpred = factory_.createExprPred(condExpr);
    
    return andPred(dcp, ifpred);
  }
    
  /**
   * The production for schema binding expressions is as follows:
   * BindExpr : \lblot x == E1; ... \rblot
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\lblot x == E1; ... \rblot) \iff DC(E1) \land ....
   *
   * The RHS of this equivalence is the result this method returns.
   * Note that in Standard Z the list of bindings is represented 
   * through a list of ConstDecl (inforced through parsing).
   *
   */
  public Pred visitBindExpr(BindExpr term)
  {
    ZDeclList constdecl = term.getZDeclList();
    
    assert isConstDeclOnly(constdecl) : "Parsing must only allow ConstDecl within the LetExpr ZDeclList!";   
    
    return dc(constdecl);
  }
  
  /**
   * The production for reference expressions is as follows:
   * RefExpr : S[E1, ...] or S
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(S[E1, ...]) \iff DC(E) \land ....
   *
   * The RHS of this equivalence is the result this method returns.
   *
   */
  public Pred visitRefExpr(RefExpr term) 
  {
    return dc(term.getZExprList());
  }
  
  /**
   * The production for schema expressions or schema constructions is as follows:
   * SchExpr: [ D | P ] or just S
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(S \defs SE) \iff DC(SE), which is just a SchText as below
   * DC([ D | P ])  \iff DC(D) \land (\forall D @ DC(P))
   *
   * The RHS of this equivalence is the result this method returns.
   *
   */
  public Pred visitSchExpr(SchExpr term) 
  {
    return dc(term.getZSchText());
  }
  
  /** 
   * DC for NumExpr is just true, despite Z/EVES not mentioning them.
   * Yet, the Standard Z BNF specifies that NumExpr are formed by 
   * numerals, which may be jokers. So, in here, we are only concerned
   * with ZNumeral, which is just true. In case of jokers, no visitor
   * will match, visitTerm(Term) will be used and "false" returned!
   *
   * The ZNumeral is useful because not always a NumExpr should be 
   * a \num. It may as well be a real number! So Numeral is just 
   * a place holder for something under Arithmos, which in the case
   * of ZNumeral is a BigInt (for representing \num).
   */
  public Pred visitNumExpr(NumExpr term) 
  {
    return dc(term.getZNumeral());
  }  
  
  /** PREDICATE TERMS */  
  
  /**
   * This implements conjunction:
   * AndPred : P \land Q
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(P \land Q)  \iff DC(P) \land (P \implies DC(Q))
   *
   * The RHS of this equivalence is the result this method returns.
   * Note that this favours evaluation of predicates from the left.
   * That is, once you know DC(P) is okay, assume it for DC(Q) in
   * case it may be useful. In this sense, we are talking about a
   * non-commutative And, since it is evaluated left-to-right here.
   *
   * IMPORTANT NOTE:
   *
   * In practice, that means ordering your predicates may affect the
   * DC conditions to be better (if Q depends on P and P appears first) 
   * or to the worst (if Q depends on P and Q appears first). Although
   * nothing is said about this in the Z/EVES manual, this can be easily
   * observed if dependant conjunctions are constructed naively. This
   * approach is similarly observed within the remaining logical connectives.
   *
   */
  public Pred visitAndPred(AndPred term)
  {
    return impliedPred2DC(term.getLeftPred(), term.getRightPred());
  }
  
  /**
   * This implements implication:
   * ImpliesPred : P \implies Q
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(P \implies Q)  \iff DC(P) \land (P \implies DC(Q))
   *
   * The RHS of this equivalence is the result this method returns.
   *
   */
  public Pred visitImpliesPred(ImpliesPred term)
  {
    return impliedPred2DC(term.getLeftPred(), term.getRightPred());
  }  
  
  /**
   * This implements disjunction:
   * OrPred : P \lor Q
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(P \lor Q)  \iff DC(P) \land (P \lor DC(Q))
   *
   * The RHS of this equivalence is the result this method returns.
   *
   */
  public Pred visitOrPred(OrPred term)
  {
    Pred p = term.getLeftPred();
    Pred dcp = dc(p);                          // DC(P)
    Pred dcq = dc(term.getRightPred());        // DC(Q)
    Pred orpq = factory_.createOrPred(p, dcq); // (P \lor DC(Q))
    return andPred(dcp, orpq);                 // DC(P) \land (P \lor DC(Q))    
  }
  
  /**
   * This implements equivalence:
   * IffPred : P \iff Q
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(P \iff Q)  \iff DC(P) \land DC(Q)
   *
   * The RHS of this equivalence is the result this method returns.
   * As equivalence would imply mutual dependency, the order in which
   * it is declared does not affect DC calculation, henc commutativity
   * of conjunction for DC is re-established.
   *
   */
  public Pred visitIffPred(IffPred term)
  {
    Pred dcp = dc(term.getLeftPred()); // DC(P)
    Pred dcq = dc(term.getRightPred());// DC(Q)
    return andPred(dcp, dcq);          // DC(P) \land DC(Q)
  }  
    
  /**
   * This implements various quantified predicate productions:
   * ExistsPred : \exists   D | P @ Q, 
   * Exists1Pred: \exists_1 D | P @ Q
   * ForallPred : \forall   D | P @ Q
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(qnt D | P @ Q) \iff DC(D) \land (\forall D @ DC(P) \land (P \implies DC(Q))) 
   *
   * The RHS of this equivalence is the result this method returns.
   * 
   */
  public Pred visitQntPred(QntPred term)
  {
    return impliedZSchTextDC(term.getZSchText(), term.getPred());
  }
  
  /**
   * This implements negation:
   * NegPred : \lnot P 
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(\lnot P)  \iff DC(P)
   *
   * The RHS of this equivalence is the result this method returns.
   *
   */
  public Pred visitNegPred(NegPred term)
  {
    return dc(term.getPred());
  }

  /**
   * This implements relational operators (i.e. prefix PR and infix IR):
   * MemPred: PR E, and E1 IR E2 ; where IR could be \in, =, or RelOp
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(E1 IR E2)  \iff DC(E1) \land DC(IR) \land DC(E2)
   * DC(PR E)      \iff DC(E) \land DC(PR)
   *
   * The RHS of this equivalence is the result this method returns.
   *
   * In Standard Z, those relational operators are just represented
   * ad MemPred. For IR, MemPred could be either membership (\in),
   * equality (=), or any relational operator (i.e. _ &lt; _, Z/EVES inrel). 
   * The first two cases DC(IR) is just true, since this is just a name. The
   * last case, however, falls into the RefExpr prodcution, where
   * generic actual expressions must be checked. Similarly, PR can only
   * be some generic prefix operator (i.e. id _, Z/EVES prerel).
   *
   */
  public Pred visitMemPred(MemPred term)
  {
    assert ZUtils.isMemPredValid(term) : "Invalid MemPred! It is neiter: equality, membership, or relational operator application." ;
    
    Expr expr1 = ZUtils.getMemPredLHS(term);// just getLeftExpr().
    Expr expr2 = ZUtils.getMemPredRHS(term);// for equality, unpacks singleton set!    
    
    Pred dce1 = dc(expr1); // DC(E1)
    Pred dce2 = dc(expr2); // DC(E2)
    
    // For the infix relation, it can be either: \in, =, or RelOp
    // For \in and =, there is no DC to perform. For RelOp, which is a RefExpr,
    // we need to check the (possible) generic instantiations. 
    Pred dcIR = (ZUtils.isRelOpApplPred(term) ? dc(ZUtils.getRelOpName(term)) : truePred());    // DC(IR)
    
    return andPred(dce1, andPred(dcIR, dce2));
  }

  /**
   * ExprPred is never created by some user expression, but through parsing 
   * in order to embed expressions within the predicate term subtree. In DC
   * calculation, we need to encapsulate some expressions as predicates
   * since the the syntactic category where the DC falls expects a predicate
   * for what only an expression can be create (i.e. LetExpr, and CondExpr).
   * For Z/EVES this is not a problem since the Expr and Pred subtree a 
   * somewhat duplicated to cope with such cases. Therefore, the DC for 
   * ExprPred OUGHT NOT to perform any further calculation, but to return
   * the expression/predicate as it is (i.e. result is the term itself!).
   */
  public Pred visitExprPred(ExprPred term) 
  {
    return term;
  }
}
