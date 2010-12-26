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

package net.sourceforge.czt.vcg.z.transformer.dc;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.vcg.z.transformer.ZPredTransformer;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;

/**
 * Z-Centric Pred transformers and auxiliary methods for Z Domain Check VCG.
 *
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public class ZPredTransformerDC extends ZPredTransformer
{
  public ZPredTransformerDC(Factory factory, Visitor<Pred> termV)
  {
    super(factory, termV);
  }

  /**
   * Creates a common implied predicate used in some DC calculations
   * for the predicate tree.
   *
   * DC(P) \land (P \implies DC(Q))
   * @param p
   * @param q
   * @return
   */
  public Pred impliedPred2DC(Pred p, Pred q)
  {
    assert p != null && q != null : "Invalid ImpliesPred elements (null)!";
    Pred dcp = visit(p); // DC(P)
    Pred dcq = visit(q); // DC(Q)
    return andPred(dcp, impliesPred(p, dcq));
  }

  /**
   * Creates a common implied predicate (see similar method below), yet
   * there is a special case (i.e. SetCompExpr), where the the DC(E) is
   * just true (i.e. \{ D | P \} for the usual \{ D | P @ E \}).
   * @param schText
   * @return
   */
  public Pred impliedZSchTextDC(ZSchText schText)
  {
    return impliedZSchTextDC(schText, truePred());
  }

  /**
   * Creates a common implied predicate used in some DC calculations.
   * That is, given the term "(D | P) @ E", it creates the following
   * DC condition predicate:
   *
   * DC(D) \land \forall D @ DC(P) \land (P \implies DC(E))
   *
   * Note that E may also be a predicate, hence we expect a Term
   * @param schText
   * @param term
   * @return
   */
  public Pred impliedZSchTextDC(ZSchText schText, Term term)
  {
    assert schText != null && term != null : "Invalid ZSchText or term (null)!";
    ZDeclList decl = schText.getZDeclList();

    // a schema text might have null pred, in which case
    // that corresponds to [D | true]. So, instead of
    // returning null, the schText.getPred() returns true
    Pred pred = getZSchTextPred(schText);

    Pred dcd = visit(decl); // DC(D)
    Pred dcp = visit(pred); // DC(P)
    Pred dce = visit(term); // DC(E)
    Pred forAll = forAllPred(decl, andPred(dcp, impliesPred(pred, dce))); // \forall D @ DC(P) \land (P \implies DC(e))

    return andPred(dcd, forAll);
  }
}
