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
import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;

/**
 * Interface characterising VC collection semantics for CZT Terms.
 * It is a kind of term visitor.
 *
 * @param <T> subtype of Type2 determining the kind VCContext for VCs being generated as Pred
 * @param <B> kind of bindinds to consider from VCContext (i.e. FSB or RREF, see VCContext)
 * @author Leo Freitas
 * @date Dec 24, 2010
 */
public interface VCCollector<//R, 
								T, B> extends TermVisitor<Pred>//<R>
{

  VCNameFactory getVCNameFactory();
  void setVCNameFactory(VCNameFactory vcf);
  
  VCGContext<T, B> getVCGContext();
  
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
  VC<Pred> calculateVC(Term term, List<? extends InfoTable> tables) throws VCCollectionException;

  /**
   * Given a paragraph and a VC, creates the underlying VC object.
   * @param vcId 
   * @param term
   * @param type
   * @param vc
   * @return
   * @throws VCCollectionException
   */
  VC<Pred> createVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException;

  /**
   * Visits a given term.  As some Z productions have null terms, like
   * AxPara \begin{axdef} x: \nat \end{axdef} has null predicate, implementations
   * should take care of such situations accordingly.
   * @param term
   * @return
   */
  Pred visit(Term term);

  TermTransformer<Pred> getTransformer();

  long getVCCount();

  void resetVCCount();

  /**
   * Any added paragraph during VC generation with an associated index for ease of
   * insertion in derived Z sections
   * @return
   */
  List<? extends Para> addedPara();
}
