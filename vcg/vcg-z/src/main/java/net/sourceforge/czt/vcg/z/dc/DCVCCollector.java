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
package net.sourceforge.czt.vcg.z.dc;

import java.util.Arrays;
import java.util.List;
import java.util.SortedSet;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.TermTransformer;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCGContext;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.transformer.dc.ZPredTransformerDC;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
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
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Qnt1Expr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.Fixity;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BindExprVisitor;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.CondExprVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
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
 * <p>
 * One should always call visit(term.???) rather than directly with term.??? because
 * some terms have null parts, which are to be ignored. visit(null) takes care of that.
 * </p>
 * @author leo
 */
public class DCVCCollector extends TrivialDCVCCollector implements
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
  ExprPredVisitor<Pred>//,
  //DomainCheckPropertyKeys
{

  /** 
   * We follow Z/EVES' approach and use the appliesTo function for
   * domain checks over unresolved names. This function is defined 
   * under the dc_toolkit.tex
   */
  private static final String APPLIESTO_NAME_INFIX = ZString.ARG_TOK + "appliesTo" + ZString.ARG_TOK;
  private static final String APPLIESTO_NAME_NOFIX = "appliesToNofix"; // this name is UNICODE, not LaTeX from DC_toolkit!
  private static final String DOM_NAME = "dom";
    
  private boolean infixAppliesTo_;
  private ZName appliesToOpName_;

  private final ZName domName_;
  private final ZPredTransformerDC predTransformer_;
    
  /**
   * 
   */
  public DCVCCollector()
  {
    this(ZUtils.createConsoleFactory());
  }  
  
  /** Creates a new instance of DCTerm
   * @param factory 
   */
  public DCVCCollector(Factory factory)
  {
    super(factory);
    domName_ = factory.createZName(DOM_NAME); // not an operator (see relation_toolkit.tex)!
    setInfixAppliesTo(PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT);
    predTransformer_ = new ZPredTransformerDC(factory, this);
    predTransformer_.setApplyTransformer(PROP_VCG_DOMAINCHECK_APPLY_TRANSFORMERS_DEFAULT);
  }

  @Override
  public TermTransformer<Pred> getTransformer()
  {
    return predTransformer_;
  }

  public boolean isAppliesToInfix()
  {
    return infixAppliesTo_;
  }

  protected final void setInfixAppliesTo(boolean value)
  {
    infixAppliesTo_ = value;
    // is it (f appliesTo x) or (f, x) \in appliesToNoFix?
    appliesToOpName_ = getZFactory().createZName(infixAppliesTo_ ? APPLIESTO_NAME_INFIX : APPLIESTO_NAME_NOFIX);
  }
  
  /** AUXILIARY TERM FACTORY METHODS */
  
   static final String[] TOTAL_OPS   = { ZString.FUN, ZString.SURJ, ZString.INJ, ZString.BIJ };
   static final String[] PARTIAL_OPS = { ZString.PFUN, ZString.PSURJ, ZString.PINJ };

  protected enum ApplType { TOTAL, PARTIAL, RELATIONAL };

  // f(g(h(v)) -> g(h(v)) => g
  //   g(h(v)) -> h(v)    => h
  //     h(v)  -> v       => v (not nested) [error?]
//  public static RefExpr getNestedApplExprName(Term term)
//  {
//    Expr result = null;
//    if (ZUtils.isNestedApplExpr(term))
//    {
//      ApplExpr appl = (ApplExpr)term;
//      if (!(appl.getLeftExpr() instanceof ApplExpr))
//        throw new UnsupportedAstClassException("Invalid Nested ApplExpr " + term);
//
//      ApplExpr nested = (ApplExpr)appl.getLeftExpr();
//
//    }
//    if (ZUtils.isApplExpr(term) && ZUtils.isApplicationExprValid((ApplExpr) term))
//    {
//      ApplExpr appl = (ApplExpr)term;
//      result = appl.getLeftExpr();
//
//      if (isApplExpr(result) && ZUtils.isNestedApplExpr(term))
//
//      // either it's is a RefExpr or a nested ApplExpr. If neither, then error!
//      // ! (!isRefExpr(result) => isApplExpr(result) && isNestedApplExpr(term))
//      if (!(isRefExpr(result) || (isApplExpr(result) && isNestedApplExpr(term))))
//        throw new UnsupportedAstClassException("Invalid ApplExpr " + term);
//    }
//    return (RefExpr)result;
//
//  }
//
//  // nested application expressions
//  protected ApplType calculateApplApplicationType(ApplExpr appl)
//  {
//    ApplType result = ApplType.RELATIONAL;
//    if (defTable_ != null)
//    {
//      ZUtils.getApplExprRef(appl);
//    }
//    return result;
//  }
//
  // usual application expressions
  protected ApplType calculateRefApplicationType(RefExpr refName)
  {
    ApplType result = ApplType.RELATIONAL;
    if (getDefTable() != null)
    {
      // attempt retrieving using usual toString?
      Definition def = getDefTable().lookupName(refName.getZName());

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
            Fixity fixity = opName.getFixity();
            // if it has fixture, check weather to get first, last or middle argument
            if (!fixity.equals(Fixity.NOFIX))
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

  /** VC COLLECTOR METHODS
   * @param vc
   * @return
   * @throws VCCollectionException
   */
  
  //@Override
  //public VCGContext<Type2, SortedSet<Definition>> getVCGContext()
  //{
	//  return super.getVCGContext();
  //}

  @Override
  protected VCType getVCType(Pred vc) throws VCCollectionException
  {
    return VCType.NONE;
  }

  @Override
  public VC<Pred> createVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException
  {
    assert type.equals(VCType.NONE);
    return super.createVC(vcId, term, type, vc);
  }

  //@Override
  //protected void beforeCalculateVC(Term term, List<? extends InfoTable> tables)
  //        throws VCCollectionException
  //{
  //  super.beforeCalculateVC(term, tables);
  //  // no need to check for null defTable_
  //}

  /** PARAGRAPH VISITING METHODS */
  
  /** 
   * Calculates DC for given term (i.e. visits term). As some Z productions have
   * null terms, like AxPara \begin{axdef} x: \nat \end{axdef} has null predicate,
   * implementations should take care of such situations accordingly. For null terms
   * in this collector, we presume a harmless DC condition (e.g., true).
   * @param term
   * @return
   */
  @Override
  public Pred visit(Term term)
  {
    if (term == null)
    {
      // for null terms, warn, but assume harmless (E.g., no VCs to be generated)
      getLogger().finest("VCG-DCCOL-NULL-TERM");
      return predTransformer_.truePred();
    }
    else
    {
      return predTransformer_.visit(term);
    }
  }

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
  //  return predTransformer_.truePred();
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
    return visit(term.getPred());
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
  @Override
  public Pred visitFreePara(FreePara term)
  {
    return visit(term.getFreetypeList());
  }
  
  /** DC a list of Freetype from a FreePara */
  @Override
  public Pred visitZFreetypeList(ZFreetypeList term)
  {
    return predTransformer_.andPredList(term);
  }
  
  /** DC the branch list of each individual Freetype */
  @Override
  public Pred visitFreetype(Freetype term) 
  {
    return visit(ZUtils.assertZBranchList(term.getBranchList()));
  }
  
  /** DC a list of Branch from a Freetype */
  @Override
  public Pred visitZBranchList(ZBranchList term)
  {
    return predTransformer_.andPredList(term);
  }
  
  /** DC the expression E on a Freetype branch  "b \ldata E \rdata" as "DC(E)". */
  @Override
  public Pred visitBranch(Branch term)
  {
    // constructors need dc, names don't
    if (term.getExpr() != null)
    {
      return visit(term.getExpr());
    }
    else
    {
      return predTransformer_.truePred();
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
  @Override
  public Pred visitAxPara(AxPara term)
  {    
    switch (term.getBox()) 
    {
      case AxBox:
        // for AxBox (axdef and gendef), use getAxBoxXXX methods
        ZDeclList decl = ZUtils.getAxBoxDecls(term);
        Pred pred = ZUtils.getAxBoxPred(term);
        
        Pred dcd = visit(decl); // DC(D)
        Pred dcp = visit(pred); // DC(P)

        // DC(D) \land (\forall D @ DC(P))
        return predTransformer_.andPred(dcd, predTransformer_.forAllPred(decl, dcp));

      case SchBox:
        // for SchBox (schema), use use getSchDefExpr methods
        Expr schExpr = ZUtils.getSchemaDefExpr(term);
        
        // for SchBox, expr must be an SchExpr! Well-formed/parsed ASTs should never suffer from this.
        if (!(schExpr instanceof SchExpr))
          throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-APPLEXPR-NOSCHEXPR = " + term));
        //assert (schExpr instanceof SchExpr) : "Invalid SchBox AxPara, no SchExpr within ConstDecl!";
        
        // for SchBox : DC([ D | P ]) \iff DC(D) \land (\forall D @ DC(P)), which comes from ZSchText DC in SchExpr ;)
        return visit(schExpr);

      case OmitBox:
        // for OmitBox (horiz. def or abbreviations), use getSchemaDefExpr method
        // This can be either a SchExpr (for horizontal definitions) or other abbreviation.        
        
        // If this is a SchExpr...
        Expr horizExpr = ZUtils.getSchemaDefExpr(term);        
        // or else it is an abbreviation
        if (horizExpr == null)
          horizExpr = ZUtils.getAbbreviationExpr(term);

        if (horizExpr == null)
          throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-APPLEXPR-NULL-HORIZEXPR = " + term));
        //assert horizExpr != null : "Invalid horizontal definition: neither schema construction, nor abbreviation (null)!";
        
        // for OmitBox: DC(n[X] == E) \iff DC(E), where E could be a SchExpr ([ D | P])
        return visit(horizExpr);
        
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
  @Override
  public Pred visitZSchText(ZSchText term) 
  {
    ZDeclList decl = term.getZDeclList();
    Pred pred = term.getPred();
    
    //assert pred != null : "Invalid schema text predicate";
    
    Pred dcd = visit(decl); // DC(D)
    
    // case the pred within the given ZSchText is null,
    // which happens in some productions like ConstDecl,
    // just result in "true", which is harmless.
    Pred dcp = visit(pred); // DC(P)
    
    // DC(D) \land (\forall D @ DC(P))
    return predTransformer_.andPred(dcd, predTransformer_.forAllPred(decl, dcp));
  }
  
  /** 
   * For operator template paragraphs, we just return true.
   * Z/EVES do not mention this, but they would be the "\syndef"
   * Z/EVES operators. We also check that the precedences are 
   * non-negative (i.e. assert it).
   */
  //@Override
  //public Pred visitOptempPara(OptempPara term)
  
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
  @Override
  public Pred visitZDeclList(ZDeclList term)
  {
    return predTransformer_.andPredList(term);
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
  @Override
  public Pred visitVarDecl(VarDecl term)
  {
    return visit(term.getExpr());
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
  @Override
  public Pred visitConstDecl(ConstDecl term)
  {
    return visit(term.getExpr());
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
  @Override
  public Pred visitInclDecl(InclDecl term)
  {
    return visit(term.getExpr());
  }
  
  /** EXPRESSION TERMS */
  
  @Override
  public Pred visitZExprList(ZExprList term) 
  {
    return predTransformer_.andPredList(term);
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
  @Override
  public Pred visitExpr2(Expr2 term)
  {
    return predTransformer_.andPred(visit(term.getLeftExpr()), visit(term.getRightExpr()));
  }
  
  /**
   * Application expression is one of the most important cases
   * as it handles function application (potentially) outside
   * their domains, which is the main point of domain checks.
   *
   * This also covers what in Z/EVES are called IR/PR for infix
   * and prefix relational operators. RefExpr as generic instantiations
   * do not need domain check (E.g., \emptyset [X]).
   *
   */
  @Override
  public Pred visitApplExpr(ApplExpr term) 
  {
    if (!ZUtils.isApplicationExprValid(term))
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-APPLEXPR-INVALID = " + term));
    //assert ZUtils.isApplicationExprValid(term) : "Invalid ApplExpr! It is neiter function operator application, nor an application expression.";

    // retrieve f and a, in f~a, or a~f~b, or (_ f _)[X]~a, etc...
    Expr name = ZUtils.getApplExprRef(term);
    if (!(name instanceof RefExpr || name instanceof ApplExpr))
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-APPLEXPR-BADCALL = " + term));
    //assert name instanceof RefExpr || name instanceof ApplExpr;

    ZExprList flatArgs = ZUtils.getApplExprArguments(term); // falttens TupleExpr into a ZExprList
    
    // build basic DC: considers generic instantiation and application arguments
    // When name is ApplExpr, this covers DCs for nested appl (e.g., visit(name) will generate DC!
    Pred dcF = visit(name);     // check DC((_F_)) for generic instantiations
    Pred dcEList = visit(flatArgs); // check all (_F_) arguments 
    Pred basicDC = predTransformer_.andPred(dcF, dcEList);
    
    // by default, use f applies$to a, (i.e. defTable_ may be null)
    // NESTED applExpr always use RELATIONAL
    ApplType applType = (name instanceof ApplExpr) ? ApplType.RELATIONAL :
            calculateRefApplicationType((RefExpr)name);
    Pred applPred;
    Expr packedArgs = term.getRightExpr(); // keeps TupleExpr or just Expr in case of arity of 1    
    switch (applType) 
    {
      case TOTAL:
        applPred = predTransformer_.truePred();
        break;
      case PARTIAL:
        // args \in \dom~f
        Expr domF = getFactory().createApplication(domName_, name);        
        applPred = getFactory().createMemPred(packedArgs, domF, Boolean.FALSE);
        break;
      case RELATIONAL:
        // f applies$to a, which is defined as \_ \appliesTo \_ -> (\exists_1 y: Y @ (a, y) \in f) in dc\_toolkit    
        TupleExpr appliesToArgs = getFactory().createTupleExpr(name, packedArgs);
        
        if (isAppliesToInfix())
        {        
          // this format is like f \appliesTo args (i.e. infix operator template)
          applPred = getFactory().createRelOpAppl(appliesToArgs, appliesToOpName_); // as an operator
        }
        else
        {
          // Create the appliesTo name exlression 
          Expr appliesToRefExpr = getFactory().createRefExpr(appliesToOpName_);
          // this format is like (f, args) \in \appliesTo (i.e. membership predicate)
          applPred = getFactory().createMemPred(appliesToArgs, appliesToRefExpr, Boolean.FALSE);
        }
        break;
      default:
        throw new AssertionError("Invalid ApplType Enum (only happens if JVM failure or corrupted byte code.");
    }
    assert applPred != null;        
    return predTransformer_.andPred(basicDC, applPred);
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
  @Override
  public Pred visitExpr1(Expr1 term)
  {
    return visit(term.getExpr());
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
  @Override
  public Pred visitExpr0N(Expr0N term) 
  {    
    return visit(term.getZExprList());
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
  @Override
  public Pred visitQnt1Expr(Qnt1Expr term) 
  {
    // DC(D) \land (\forall D @ DC(P)), for [ D | P ]
    Pred dcschtext = visit(term.getZSchText());
    
    Expr expr = term.getExpr();    
    Pred dce = visit(expr); // DC(E)
    
    // DC(D) \land (\forall D @ DC(P)) \land DC(E)
    return predTransformer_.andPred(dcschtext, dce);
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
  @Override
  public Pred visitSetCompExpr(SetCompExpr term)
  {
    // this covers both cases when getExpr() is null and not
    // the impiedZSchTextDC is just like visitZSchText, but with the extra expr
    return predTransformer_.impliedZSchTextDC(term.getZSchText(), visit(term.getExpr()));

    //if (term.getExpr() == null) // \{ D | P \}
    //  return predTransformer_.impliedZSchTextDC(term.getZSchText());
    //else
    //  return predTransformer_.impliedZSchTextDC(term.getZSchText(), term.getExpr());
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
  @Override
  public Pred visitLambdaExpr(LambdaExpr term) 
  {
    // shouldn't be null (e.g., not well parsed) but if it is, just return true for getExpr()
    //assert term.getExpr() != null : "Invalid LambdaExpr getExpr() term (null)!";
    return predTransformer_.impliedZSchTextDC(term.getZSchText(), visit(term.getExpr()));
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
  @Override
  public Pred visitLetExpr(LetExpr term) 
  {
    if (term.getZSchText() == null)
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-LETEXPR-ZSCHTXT-NULL = " + term));

    // Check for the expressions within the list of declaration
    ZDeclList constdecl = term.getZSchText().getZDeclList();

    if (!(predTransformer_.isOnlyConstDecl(constdecl)))
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-LETEXPR-NOCONSTDECL = " + term));
    //assert predTransformer_.isOnlyConstDecl(constdecl) : "Parsing must only allow ConstDecl within the LetExpr ZDeclList!";

    if (term.getZSchText().getPred() != null)
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-LETEXPR-ZSCHTXT-NONNULL-PRED = " + term));
    //assert term.getZSchText().getPred() == null : "Parsing must set SchText.Pred on LetExpr to null!";
    
    Pred dcd = visit(constdecl);     // DC(D)
    Pred dce = visit(term.getExpr());// DC(E)
    
    // (\LET x == E1, ... @ DC(E)), as an expression to be transformed in a predicate
    LetExpr letexpr = getFactory().createLetExpr(term.getZSchText(),
            predTransformer_.predAsSchExpr(dce));
    Pred letpred = getFactory().createExprPred(letexpr);
    
    // DC(D) \land (\LET x == E1, ... @ DC(E))
    return predTransformer_.andPred(dcd, letpred);
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
  @Override
  public Pred visitMuExpr(MuExpr term) 
  {
    if (term.getZSchText() == null)
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-MUEXPR-ZSCHTXT-NULL = " + term));

    // Pred for Mu could NOT be null!
    if (term.getZSchText().getPred() == null)
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-MUEXPR-ZSCHTXT-NULL-PRED = " + term));
    //assert term.getZSchText().getPred() != null : "Invalid MuExpr: getPred() is null!";

    ZDeclList decl = term.getZSchText().getZDeclList();
    Pred pred      = term.getZSchText().getPred();

    //Pred dcd = visit(decl); // DC(D)
    //Pred dcp = visit(pred); // DC(P)

    // \exists_1 D | true @ P
    Pred exists1 = getFactory().createExists1Pred(getFactory().createZSchText(decl, predTransformer_.truePred()), pred);

    // (\forall D @ DC(P) \land (P \implies DC(E))) ; term.getExpr() may be null for true when D is simple (not a schema, say).
    //Pred dcAI = predTransformer_.impliedZSchTextDC(term.getZSchText(), visit(term.getExpr()));

    // DC(D) \land (\forall D @ DC(P) \land (P \implies DC(E))) \land (\exists_1 D | true @ P)
    return predTransformer_.andPred(predTransformer_.impliedZSchTextDC(term.getZSchText(), visit(term.getExpr())), exists1);
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
  @Override
  public Pred visitCondExpr(CondExpr term) 
  {
    Pred pred = term.getPred();
    Expr expr1 = term.getLeftExpr();
    Expr expr2 = term.getRightExpr();
    
    Pred dcp = visit(pred);   // DC(P)
    Pred dce1 = visit(expr1); // DC(E1)
    Pred dce2 = visit(expr2); // DC(E2);
    
    // (\IF P \THEN DC(E1) \ELSE DC(E2)), as a schema expression
    Expr condExpr = getFactory().createCondExpr(pred, 
            predTransformer_.predAsSchExpr(dce1),
            predTransformer_.predAsSchExpr(dce2));
    Pred ifpred = getFactory().createExprPred(condExpr);
    
    return predTransformer_.andPred(dcp, ifpred);
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
  @Override
  public Pred visitBindExpr(BindExpr term)
  {
    ZDeclList constdecl = term.getZDeclList();

    if (!(predTransformer_.isOnlyConstDecl(constdecl)))
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-BINDEXPR-NOCONSTDECL = " + term));
    //assert predTransformer_.isOnlyConstDecl(constdecl) : "Parsing must only allow ConstDecl within the LetExpr ZDeclList!";
    
    return visit(constdecl);
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
  @Override
  public Pred visitRefExpr(RefExpr term) 
  {
    return visit(term.getZExprList());
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
  @Override
  public Pred visitSchExpr(SchExpr term) 
  {
    return visit(term.getZSchText());
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
  @Override
  public Pred visitNumExpr(NumExpr term) 
  {
    return visit(term.getZNumeral());
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
  @Override
  public Pred visitAndPred(AndPred term)
  {
    // these two pred ought not to be null!
    return predTransformer_.impliedPred2DC(term.getLeftPred(), term.getRightPred());
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
  @Override
  public Pred visitImpliesPred(ImpliesPred term)
  {
    return predTransformer_.impliedPred2DC(term.getLeftPred(), term.getRightPred());
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
  @Override
  public Pred visitOrPred(OrPred term)
  {
    Pred p = term.getLeftPred();
    Pred dcp = visit(p);                          // DC(P)
    Pred dcq = visit(term.getRightPred());        // DC(Q)
    Pred orpq = predTransformer_.orPred(p, dcq);  // (P \lor DC(Q))
    return predTransformer_.andPred(dcp, orpq);                 // DC(P) \land (P \lor DC(Q))
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
  @Override
  public Pred visitIffPred(IffPred term)
  {
    Pred dcp = visit(term.getLeftPred()); // DC(P)
    Pred dcq = visit(term.getRightPred());// DC(Q)
    return predTransformer_.andPred(dcp, dcq);          // DC(P) \land DC(Q)
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
  @Override
  public Pred visitQntPred(QntPred term)
  {
    return predTransformer_.impliedZSchTextDC(term.getZSchText(), visit(term.getPred()));
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
  @Override
  public Pred visitNegPred(NegPred term)
  {
    return visit(term.getPred());
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
  @Override
  public Pred visitMemPred(MemPred term)
  {
    if (!ZUtils.isMemPredValid(term))
      throw new CztException(new DomainCheckException(getDialect(), "VC-DC-COL-MEMPRED-INVALID = " + term));
    //assert ZUtils.isMemPredValid(term) : "Invalid MemPred! It is neiter: equality, membership, or relational operator application." ;
    
    Expr expr1 = ZUtils.getMemPredLHS(term);// just getLeftExpr().
    Expr expr2 = ZUtils.getMemPredRHS(term);// for equality, unpacks singleton set!    
    
    Pred dce1 = visit(expr1); // DC(E1)
    Pred dce2 = visit(expr2); // DC(E2)
    
    // For the infix relation, it can be either: \in, =, or RelOp
    // For \in and =, there is no DC to perform. For RelOp, which is a RefExpr,
    // we need to check the (possible) generic instantiations. 
    Pred dcIR = (ZUtils.isRelOpApplPred(term) ? visit(ZUtils.getRelOpName(term)) : predTransformer_.truePred());    // DC(IR)
    
    return predTransformer_.andPred(dce1, predTransformer_.andPred(dcIR, dce2));
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
  @Override
  public Pred visitExprPred(ExprPred term) 
  {
    return term;
  }
}
