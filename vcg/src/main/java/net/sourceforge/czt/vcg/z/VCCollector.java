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

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.z.ast.Para;

/**
 * Interface characterising VC collection semantics for CZT Terms.
 * It is a kind of term visitor.
 *
 * TODO: What else should a collector contain?
 * @param <R> WHAT SHOULD THIS BE FOR VCs?
 * @author Leo Freitas
 * @date Dec 24, 2010
 */
public interface VCCollector<R> extends TermVisitor<R>
{

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
  VC<R> calculateVC(Term term, List<? extends InfoTable> tables) throws VCCollectionException;

  /**
   * Given a paragraph and a VC, creates the underlying VC object.
   * @param term
   * @param vc
   * @return
   * @throws VCCollectionException
   */
  VC<R> createVC(Para term, R vc) throws VCCollectionException;

  /**
   * Visits a given term.  As some Z productions have null terms, like
   * AxPara \begin{axdef} x: \nat \end{axdef} has null predicate, implementations
   * should take care of such situations accordingly.
   * @param term
   * @return
   */
  R visit(Term term);

  TermTransformer<R> getTransformer();
}
