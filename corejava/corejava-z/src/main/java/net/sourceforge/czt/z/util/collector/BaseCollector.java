/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.z.util.collector;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.CztLogger;

/**
 * <p>
 * Base class of collectors. It implements the general contract for
 * ListTerm by visiting each term, and the general contract for Term
 * by doing nothing.
 * </p>
 * <p>
 * Derived collector classes need to implement the visitor of the particular
 * term they are responsible to collect. For every collected item, the class
 * needs to have a corresponding collected element (or just a List) as a protected 
 * field. This protected object is used by the XXXElements hierarchy to give access
 * to the underlying information in a structured way.
 * </p>
 * @param <R>
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public class BaseCollector<R> implements
        TermVisitor<R>, ListTermVisitor<R>
{

  BaseCollector()
  {
  }

  @Override
  public R visitTerm(Term term)
  {
    CztLogger.getLogger(this.getClass()).warning("Hit visitTerm for " + term.getClass() + " : " + term);
    return null;
  }

  @Override
  @SuppressWarnings("rawtypes")
  public R visitListTerm(ListTerm term)
  {
    for (Object o : term)
    {
      if (o instanceof Term)
        ((Term)o).accept(this);
      else
        visitNonTerm(o);
    }
    return null;
  }

  public <T extends Term> R visit(T term)
  {
    R result = null;
    if (term != null)
      result = term.accept(this);
    return result;
  }
  public R visitNonTerm(Object obj)
  {
    assert !(obj instanceof Term);
    return null;
  }
}
