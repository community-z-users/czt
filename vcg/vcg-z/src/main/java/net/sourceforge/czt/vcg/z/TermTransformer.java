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

package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.util.Factory;

/**
 * Top-level term transformation interface. TODO: maybe have it like AST / AST-IMPL packages?
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public interface TermTransformer<R>
{

  Factory getFactory();

  /**
   * Flag determining whether to apply transformer or not. That means implementations
   * ought to provide alternative (e.g., conservative) solutions when not transforming terms.
   * @return
   */
  boolean isApplyingTransformer();
  void setApplyTransformer(boolean value);

  //R transform(R... term);

  /**
   * Returns a visitor implementing a VCG protocol.
   * @param <R>
   * @param resClass
   * @return
   */
  Visitor<R> getTermVisitor();

  /**
   * Visit the given term. At this point only non-null terms are allowed.
   * Default values for null terms are to be handled by corresponding collector classes.
   * @param term
   * @return
   * @throws CztException if term is null
   */
  R visit(Term term);
}
