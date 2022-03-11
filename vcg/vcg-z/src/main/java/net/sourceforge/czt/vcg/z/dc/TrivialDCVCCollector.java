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

import java.util.SortedSet;

import net.sourceforge.czt.vcg.util.DefaultVCNameFactory;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.TrivialVCCollector;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCConfig;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.Fact;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZNumeral;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.DirectiveVisitor;
import net.sourceforge.czt.z.visitor.FactVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NameSectTypeTripleVisitor;
import net.sourceforge.czt.z.visitor.NameTypePairVisitor;
import net.sourceforge.czt.z.visitor.NewOldPairVisitor;
import net.sourceforge.czt.z.visitor.OperVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZNumeralVisitor;

/**
 *
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public abstract class TrivialDCVCCollector extends 
			// ContextType, ContextBindingType
			TrivialVCCollector<Type2, SortedSet<Definition>> implements
        DomainCheckPropertyKeys,
        LatexMarkupParaVisitor<Pred>,
        GivenParaVisitor<Pred>,
        ThetaExprVisitor<Pred>,
        FactVisitor<Pred>,
        //Visitor<Pred>,
        NameTypePairVisitor<Pred>,
        NameSectTypeTripleVisitor<Pred>,
        OperVisitor<Pred>,
        ZNameVisitor<Pred>,
        DirectiveVisitor<Pred>,
        ZNameListVisitor<Pred>,
        NewOldPairVisitor<Pred>,
        ZNumeralVisitor<Pred>
{

  /** Creates a new instance of TrivialVCCollector
   * @param factory
   */
  public TrivialDCVCCollector(Factory factory)
  {
    super(factory);
    setVCNameFactory(new DefaultVCNameFactory(
        VCG_DOMAINCHECK_VCNAME_SUFFIX, VCG_DOMAINCHECK_SOURCENAME_SUFFIX));
  }

  @Override
  public Pred visitLatexMarkupPara(LatexMarkupPara term)
  {
    return truePred();
  }

  @Override
  public Pred visitGivenPara(GivenPara term)
  {
    return truePred();
  }

  /**
   * This implements ThetaExpr for schemas:
   * ThetaExpr: \theta S
   *
   * which in Z is given as
   *
   * DC(\theta S) \iff true
   *
   * The RHS of this equivalence is the result this method returns
   */
  @Override
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
  @Override
  public Pred visitFact(Fact term)
  {
    return truePred();
  }

  @Override
  public Pred visitNameTypePair(NameTypePair term)
  {
    return truePred();
  }

  @Override
  public Pred visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    return truePred();
  }

  @Override
  public Pred visitOper(Oper term)
  {
    return truePred();
  }

  @Override
  public Pred visitZName(ZName term)
  {
    return truePred();
  }

  @Override
  public Pred visitDirective(Directive term)
  {
    return truePred();
  }

  @Override
  public Pred visitZNameList(ZNameList term)
  {
    return truePred();
  }

  @Override
  public Pred visitNewOldPair(NewOldPair term)
  {
    return truePred();
  }

  /**
   * for numbers is just true, despite Z/EVES not mentioning them.
   */
  @Override
  public Pred visitZNumeral(ZNumeral term)
  {
    return truePred();
  }

  @Override
  protected Pred calculateVC(Para term) throws VCCollectionException
  {
    Pred vc = super.calculateVC(term);
    
    if (vc.getAnn(VCConfig.class) == null) {
      // no VC config set, mark it as DC default
      vc.getAnns().add(new VCConfig(VCTYPE_DC_DEFAULT, Precedence.AFTER));
    }
    
    return vc;
  }
}
