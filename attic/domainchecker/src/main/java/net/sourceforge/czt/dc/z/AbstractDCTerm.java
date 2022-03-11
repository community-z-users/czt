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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * Abstract domain check term. 
 *  
 * @param <R> 
 * @author leo
 */
public abstract class AbstractDCTerm<R> implements Visitor<R>, TermVisitor<R>
{  
  protected Factory factory_;
    
  /** Creates a new instance of AbstractDCTerm
   * @param factory 
   */
  public AbstractDCTerm(Factory factory)
  {
    if (factory == null)
    {
      throw new IllegalArgumentException("Cannot create domain check term with a null factory");
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
  
  /** Creates a TruePred (i.e. true)
   * @return 
   */
  protected Pred truePred()
  {
    return factory_.createTruePred();
  }
  
  /**
   * For terms in general, just assume nothing is known about them,
   * hence their DC is the worst possible (i.e. false). That means,
   * if our implementation fails to recognise some term, it will 
   * always lead to a safe result (i.e. an impossible DC to prove!).
   *
   * An alternative implementation would be to raise an exception.
   * We will chose this one for now.
   * @param term 
   */
  @Override
  public R visitTerm(Term term)
  { 
    throw new CztException(new DomainCheckException("DC-NOVISITOR-ERROR = " + term.getClass().getSimpleName()));
  }
}