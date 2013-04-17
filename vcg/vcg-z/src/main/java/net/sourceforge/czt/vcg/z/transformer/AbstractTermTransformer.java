/*
  Copyright (C) 2008 Leo Freitas
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
package net.sourceforge.czt.vcg.z.transformer;


import net.sourceforge.czt.vcg.z.TermTransformer;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.util.Factory;

/**
 * Abstract class for VCG Term transformation. For instance, Predicate transformers
 * are often used to simplify potential VCs.
 *
 * @param <R>
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public abstract class AbstractTermTransformer<R> implements TermTransformer<R>
{

  /**
   * Factory object creating transformed terms. Because it is often used,
   * we also provide direct access (e.g., protected field). Since it is final,
   * it is okay.
   */
  protected final Factory factory_;
  protected final Visitor<R> termVisitor_;

  /**
   * Flag determining whether to apply this transformer or not
   */
  private boolean applyTransformer_;

  /**
   * 
   * @param factory
   * @param termV
   */
  protected AbstractTermTransformer(Factory factory, Visitor<R> termV)
  {
    if (factory == null || termV == null)
    {
      throw new IllegalArgumentException("VCG-PREDTRS-NULL-PARAMS");
    }
    factory_ = factory;
    applyTransformer_ = false;
    termVisitor_ = termV;
  }

  @Override
  public Factory getFactory()
  {
    return factory_;
  }

  /**
   * Flag determining whether to apply transformer or not. That means implementations
   * ought to provide alternative (e.g., conservative) solutions when not transforming terms.
   * @return
   */
  @Override
  public boolean isApplyingTransformer()
  {
    return applyTransformer_;
  }

  @Override
  public void setApplyTransformer(boolean value)
  {
    applyTransformer_ = value;
  }

  @Override
  public Visitor<R> getTermVisitor()
  {
    return termVisitor_;
  }

  @Override
  public R visit(Term term)
  {
    assert term != null : "VCG-TRANS-NULL-TERM";
    return term.accept(termVisitor_);
  }
}
