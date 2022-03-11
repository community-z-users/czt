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
package net.sourceforge.czt.vcg.z;

import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.AnnVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.TypeVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.ZStrokeListVisitor;

/**
 * Trivial Term VC generator. It returns true for all predicates that have
 * trivial/irrelevant VCs, like narrative text. This is different from a
 * default result, which if present at all, ought to be false (the strongest
 * possible VC) or an exception. That's what AbstractVCCollector does.
 *
 * @author leo
 */
public abstract class TrivialVCCollector<T, B> extends AbstractVCCollector<//Pred, 
																				T, B>
        implements
        UnparsedParaVisitor<Pred>,
        NarrParaVisitor<Pred>,
        TypeVisitor<Pred>,
        AnnVisitor<Pred>,
        StrokeVisitor<Pred>,
        ZStrokeListVisitor<Pred>,
        OptempParaVisitor<Pred>//,
        //TermVisitor<Pred>
{

  /** Creates a new instance of TrivialVCCollector
   * @param factory 
   */
  public TrivialVCCollector(Factory factory)
  {
    super(factory);
  }

  /** Creates a TruePred (i.e. true)
   * @return
   */
  protected Pred truePred()
  {
    return getFactory().createTruePred();
  }

  @Override
  protected Pred calculateVC(Para term) throws VCCollectionException
  {
    return visit(term);
  }

  @Override
  public VC<Pred> createVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException
  {
    
    String configType = null;
    Precedence prec = null;
    ZNameList genParams = null;
    
    VCConfig vcConfig = vc.getAnn(VCConfig.class);
    if (vcConfig != null) {
      // TODO do something about precedence as well?
      configType = vcConfig.getType();
      prec = vcConfig.getPrecedence();
      genParams = vcConfig.getGenParams();
    }
    
    String vcName = getVCNameFactory().getVCName(term, configType);
    
    return new PredVC(vcId, term, type, vc, vcName, prec, genParams);
  }

  /**
   * For terms in general, just assume nothing is known about them,
   * hence their VC is the worst possible (i.e. false). That means,
   * if our implementation fails to recognise some term, it will
   * always lead to a safe result (i.e. an impossible VC to prove!).
   * An alternative implementation would be to raise an exception.
   * @param term
   */
  @Override
  public Pred visitTerm(Term term)
  {
    final String msg = "VCG-NOVISITOR-ERROR(@trivial) = " +term.getClass().getSimpleName() + "; creating true VC";
    getLogger().warning(msg);
    return getFactory().createTruePred();
    // don't raise exception to allow for completion of VCGing
    //throw new CztException(new VCGException(msg));
  }

  @Override
  public Pred visitOptempPara(OptempPara term)
  {
    if (term.getPrec() != null && term.getPrec().signum() < 0)
      throw new CztException(new VCCollectionException(getDialect(), "VC-TRIVIALCOL-OPTEMPPARA-NEGPREC = " + term));
    //assert term.getPrec().signum() >= 0 : "Operator template paragraph precedence MUST be non-negative";
    return truePred();
  }

  @Override
  public Pred visitUnparsedPara(UnparsedPara term)
  {
    return truePred();
  }

  @Override
  public Pred visitNarrPara(NarrPara term)
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

//AnnVisitor<Pred>,
//  SectTypeEnvAnn Visitor<R>,
//  SignatureAnnVisitor<R>,
//  LocAnnVisitor<R>,
//  ParenAnn Visitor<R>,
//  TypeAnn Visitor<R>,
  @Override
  public Pred visitAnn(Ann term)
  {
    return truePred();
  }

//StrokeVisitor<Pred>,
//  NumStroke Visitor<R>,
//  NextStrokeVisitor<R>,
//  OutStrokeVisitor<R>,
//  InStrokeVisitor<R>,
  @Override
  public Pred visitStroke(Stroke term)
  {
    return truePred();
  }

  @Override
  public Pred visitZStrokeList(ZStrokeList term)
  {
    return truePred();
  }

  @Override
  public List<? extends Para> addedPara()
  {
    return Collections.emptyList();
  }
}
