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

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.Fact;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZNumeral;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.AnnVisitor;
import net.sourceforge.czt.z.visitor.DirectiveVisitor;
import net.sourceforge.czt.z.visitor.FactVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NameSectTypeTripleVisitor;
import net.sourceforge.czt.z.visitor.NameTypePairVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NewOldPairVisitor;
import net.sourceforge.czt.z.visitor.OperVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z.visitor.TypeVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZNumeralVisitor;
import net.sourceforge.czt.z.visitor.ZStrokeListVisitor;

/**
 * Trivial domain checker predicate which just returns true. 
 * That is, all those where it is harmless to return true.
 * This is different from a default result, which if at all,
 * should be false (the strongest possible domain check) or
 * an exception.
 * @author leo
 */
public abstract class TrivialDCTerm extends AbstractDCTerm<Pred> implements
  GivenParaVisitor<Pred>,
  UnparsedParaVisitor<Pred>,
  NarrParaVisitor<Pred>,
  LatexMarkupParaVisitor<Pred>,
  TypeVisitor<Pred>,
  NameTypePairVisitor<Pred>,
  NameSectTypeTripleVisitor<Pred>,
  AnnVisitor<Pred>,
  OperVisitor<Pred>,
  ZNameVisitor<Pred>,
  DirectiveVisitor<Pred>,
  ZNameListVisitor<Pred>,
  NewOldPairVisitor<Pred>,
  StrokeVisitor<Pred>,
  ZStrokeListVisitor<Pred>,
  ZNumeralVisitor<Pred>,
  ThetaExprVisitor<Pred>,
  FactVisitor<Pred>,
  Visitor<Pred>
  {

  /** Creates a new instance of TrivialDCTerm
   * @param factory 
   */
  public TrivialDCTerm(Factory factory)
  {
    super(factory);
  }

  public Pred visitGivenPara(GivenPara term)
  {
    return truePred();
  }

  public Pred visitUnparsedPara(UnparsedPara term)
  {
    return truePred();
  }

  public Pred visitNarrPara(NarrPara term)
  {
    return truePred();
  }

  public Pred visitLatexMarkupPara(LatexMarkupPara term)
  {
    return truePred();
  }
  
//Type<Pred>,
//  PowerTypeVisitor<R>,
//  GenParamTypeVisitor<R>,
//  SchemaTypeVisitor<R>,
//  GenericTypeVisitor<R>,
//  GivenTypeVisitor<R>,
//  SignatureVisitor<R>,
//  ProdTypeVisitor<R>,
  @Override
  public Pred visitType(Type term)
  {
    return truePred();
  }

  @Override
  public Pred visitNameTypePair(NameTypePair term)
  {
    return truePred();
  }

  public Pred visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    return truePred();
  }

//AnnVisitor<Pred>,
//  SectTypeEnvAnn Visitor<R>,
//  SignatureAnnVisitor<R>,
//  LocAnnVisitor<R>,
//  ParenAnn Visitor<R>,
//  TypeAnn Visitor<R>,
  public Pred visitAnn(Ann term)
  {
    return truePred();
  }

//OperVisitor<Pred>,
//  OperatorVisitor<R>,
//  OperandVisitor<R>,
  public Pred visitOper(Oper term)
  {
    return truePred();
  }

  public Pred visitZName(ZName term)
  {
    return truePred();
  }

  public Pred visitDirective(Directive term)
  {
    return truePred();
  }

  public Pred visitZNameList(ZNameList term)
  {
    return truePred();
  }

  public Pred visitNewOldPair(NewOldPair term)
  {
    return truePred();
  }

//StrokeVisitor<Pred>,
//  NumStroke Visitor<R>,
//  NextStrokeVisitor<R>,
//  OutStrokeVisitor<R>,
//  InStrokeVisitor<R>,
  public Pred visitStroke(Stroke term)
  {
    return truePred();
  }

  public Pred visitZStrokeList(ZStrokeList term)
  {
    return truePred();
  }
  
  /** DC for numbers is just true, despite Z/EVES not mentioning them. */
  public Pred visitZNumeral(ZNumeral term) 
  {
    return truePred();
  }
  
  /**
   * This implements ThetaExpr for schemas:
   * ThetaExpr: \theta S
   * 
   * which in Z/EVES is given as
   * 
   * DC(\theta S) \iff true
   *
   * The RHS of this equivalence is the result this method returns
   */
  public Pred visitThetaExpr(ThetaExpr term) 
  {
    return truePred();
  }

  /**
   * This implements the Fact predicates:
   * TruePred : true  
   * FalsePred: false
   * 
   * This covers the Z/EVES domain check rules for:
   *
   * DC(true)  \iff true
   * DC(false) \iff true
   *
   * The RHS of this equivalence is the result this method returns.
   * Note that this leaves abstract Pred and Pred2 out of our DC checking.
   *
   */
  public Pred visitFact(Fact term)
  {
    return truePred();
  }
}

