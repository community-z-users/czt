/**
Copyright 2011, Leo Freitas
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

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.util.Factory;

/**
 * Abstract VCG for CZT terms. For unknown/unprocessed terms, it returns false
 * as the generated VC (e.g., the most difficult one to discharge).
 *  
 * @param <R>
 * @author Leo Freitas
 */
public abstract class AbstractVCCollector<R> implements VCCollector<R>
{  
  protected Factory factory_;
    
  /** Creates a new instance of AbstractVCCollector
   * @param factory 
   */
  public AbstractVCCollector(Factory factory)
  {
    if (factory == null)
    {
      throw new IllegalArgumentException("VCG-TERM-NULL-FACTORY");
    }
    factory_ = factory;
    // NOTE: not effective to change this factory, since it won't have LocAnn! Change the LocAnn factory directly instead. :-(
    //
    // get underlying ToStringVisitor of the Z factory of the given factory and set LocAnn offsets.
    //ZUtils.assertZPrintVisitor(
    //        ZUtils.assertZFactoryImpl(
    //          factory_.getZFactory()).getToStringVisitor()).setOffset(1, 1);
  }     
  
  protected Factory getZFactory()
  {
    return factory_;
  }

  /**
   * Visits the given term (e.g., <code>term.accept(this)</code>).
   * @param term term to visit
   */
  protected abstract R visit(Term term);
  
  /**
   * For terms in general, just assume nothing is known about them,
   * hence their VC is the worst possible (i.e. false). That means,
   * if our implementation fails to recognise some term, it will 
   * always lead to a safe result (i.e. an impossible VC to prove!).
   * An alternative implementation would be to raise an exception.
   * @param term 
   */
  @Override
  public R visitTerm(Term term)
  { 
    final String msg = "VCG-NOVISITOR-ERROR = " +term.getClass().getSimpleName();
    SectionManager.traceWarning(msg);
    /*return factory_.createFalsePred();*/
    throw new CztException(new VCGException(msg));
  }

  /**
   * Calculate the verification condition for a given term in the context of
   * any available information tables. These tables <b>MUST</b> come from the
   * section manager of this collector. They could be, for instance, tables for
   * definitions, operators, and other related conjectures.
   * @param term
   * @param tables
   * @throws VCCollectionException
   * @return
   */
  //public VC<R> calculateVC(Term term, List<? extends InfoTable> tables)
  //        throws VCCollectionException
  //{
  //  term.accept(this);
  //  return ?;
  //}

  protected abstract void beforeCalculateVC(Term term, List<? extends InfoTable> tables)
          throws VCCollectionException;

  protected abstract void afterCalculateVC(VC<R> vc)
          throws VCCollectionException;

  protected abstract R calculateVC(Para term) throws VCCollectionException;

  @Override
  public abstract VC<R> createVC(Para term, R vc) throws VCCollectionException;

  /**
   * Calculate the verification condition for a given term in the context of
   * any available information tables. These tables <b>MUST</b> come from the
   * section manager of this collector. They could be, for instance, tables for
   * definitions, operators, and other related conjectures.
   *
   * Runs the VC generation algorithms over the given term and definition table.
   * The definition table is important in order to make sure the types of known
   * names can be properly inspected. For instance, assuming expressions are ground
   * (i.e., just names), the VC for domain checking "x \cup y" will ultimately depend
   * on \cup being a total function or having the types of x and y within its domain.
   * The definition table should contain such declared type information. If null
   * is given, then applies$to will always be used.
   *
   * @param term
   * @param tables
   * @throws VCCollectionException
   * @return
   */
  @Override
  public VC<R> calculateVC(Term term, List<? extends InfoTable> tables)
          throws VCCollectionException
  {
    assert term != null : "Invalid term for DC";

    // only calculate for Para terms
    if (!(term instanceof Para))
    {
      throw new VCCollectionException("VC-COLLECT-NOT-PARA = " + term.getClass().getSimpleName());
    }

    // prepare prior tables
    beforeCalculateVC(term, tables);

    // calculate the actual VC contents
    Para para = (Para)term;
    R vc = null;
    try
    {
      vc = calculateVC(para);
    }
    catch (CztException e)
    {
      throw new VCCollectionException("VC-COLLECT-CALC-ERROR = " + para.toString(), e);
    }

    // create the result
    VC<R> result = createVC(para, vc);

    // finalise the calculation
    afterCalculateVC(result);

    // return result
    return result;
  }
}