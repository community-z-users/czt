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

import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.util.Factory;

/**
 * Base implementation for Pred transformers. There are many more one could add
 *
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public abstract class AbstractPredTransformer extends AbstractTermTransformer<Pred>
{

  protected AbstractPredTransformer(Factory factory, Visitor<Pred> termV)
  {
    super(factory, termV);
  }

  public Pred truePred()
  {
    return factory_.createTruePred();
  }

  /**
   * Creates a AndPred from the given arguments with And.Wedge (i.e. lhs \land rhs).
   * We apply conjunction zero, unit, and idempotent laws
   * transforming the resulting conjunction as:
   * <ul>
   *  <li>false \land P \iff false </li>
   *  <li>false \land P \iff false </li>
   *  <li>true \land P \iff P</li>
   *  <li>P \land true \iff P</li>
   *  <li>P \land P \iff P</li>
   *  <li>P \land \lnot P \iff false </li>
   * </ul>
   * These transformations are useful when chaining various predicates that
   * become spurious when applying the unit-law exhaustively.
   *
   * @param lhs left hand side predicate
   * @param rhs right hand side predicate
   * @return LHS \land RHS with And.Wedge, unless transformed
   */
  public Pred andPred(Pred lhs, Pred rhs)
  {
    assert lhs != null && rhs != null : "Invalid AndPred request!";
    Pred result = null;
    if (isApplyingTransformer())
    {
      // P \land false = \false \land P = P
      if (lhs instanceof FalsePred || rhs instanceof FalsePred)
      {
        result = factory_.createFalsePred();
      }
      // true \land RHS = RHS
      if (lhs instanceof TruePred)
      {
        result = rhs;
      }
      // LHS \land true = LHS
      else if (rhs instanceof TruePred)
      {
        result = lhs;
      }
      // LHS \land LHS = LHS
      else if (lhs.equals(rhs))
      {
        result = lhs;
      }
    }
    if (result == null)
    {
      // Leave contradiction law (P \land \lnot P) out.
      //Pred innerLHS = lhs instanceof NegPred ? ((NegPred)lhs).getPred() : lhs;
      //Pred innerRHS = rhs instanceof NegPred ? ((NegPred)rhs).getPred() : rhs;
      //if (innerLHS.equals(innerRHS))

      result = factory_.createAndPred(lhs, rhs, And.Wedge);
    }
    return result;
  }


  /**
   * Recurses through the list of terms and build an {@link #andPred(net.sourceforge.czt.z.ast.Pred, net.sourceforge.czt.z.ast.Pred)}
   * for the resulting domain check for each of them. If the list is empty or has one element it is conjoined with "true".
   * That is, for a list &lt;p, q&gt;, it creates "true \land dc(p) \land dc(q)"; whereas an
   * empty list just returns "true".
   *
   * DC(&lt;p, q, ...&gt;) = DC(p) \land DC(q) \land ...
   * @param list
   * @return
   */
  public Pred andPredList(List<? extends Term> list)
  {
    assert list != null : "Invalid ListTerm (null)!";
    Pred result = truePred();
    if (!list.isEmpty())
    {
      Iterator<? extends Term> it = list.iterator();
      assert it.hasNext();
      Term term = it.next();
      result = visit(term);
      while (it.hasNext())
      {
        term = it.next();
        result = andPred(result, visit(term));
      }
    }
    return result;
  }


  /**
   * Creates a ForAllPred with the given declarations and predicate.
   * That is, "\forall decl @ pred". We apply the simple zero-law:
   * <ul>
   *  <li>\forall D @ true \iff true </li>
   * </ul>
   * Even if D is false, this is the right transformation as anything implies true.
   * @param decl
   * @param pred
   * @return
   */
  public Pred forAllPred(ZDeclList decl, Pred pred)
  {
    assert decl != null && pred != null : "Invalid ForAllPred request!";
    // \forall D @ true \iff true (even if D is false!): Don't do it...
    Pred result = null;
    if (isApplyingTransformer())
    {
      if (pred instanceof TruePred)
      {
        result = truePred();
      }
    }
    if (result == null)
    {
      result = factory_.createForallPred(factory_.createZSchText(decl, null), pred);
    }
    return result;
  }

  /**
   * Creates an ImpliesPred from the given arguments (i.e. p \implies q)
   * We apply implication right-zero, right-unit, false-antecedent,
   * false-consequent, and reflection laws transforming the resulting
   * conjunction as:
   * <ul>
   *  <li>P \implies true \iff true </li>
   *  <li>true \implies P \iff true </li>
   *  <li>P \implies false \iff \lnot P</li>
   *  <li>false \implies P \iff true</li>
   *  <li>P \implies P \iff true</li>
   * </ul>
   * @param p
   * @param q
   * @return
   */
  public Pred impliesPred(Pred p, Pred q)
  {
    assert p != null && q != null : "Invalid ImpliesPred request!";
    Pred result = null;
    if (isApplyingTransformer())
    {
      // true ==> q     <==> q
      // p    ==> true  <==> true (which is q)
      if (p instanceof TruePred || q instanceof TruePred)
      {
        result = q;
      }
      // false ==> q     <==> true
      // P     ==> P     <==> true
      else if ((p instanceof FalsePred) || p.equals(q))
      {
        result = truePred();
      }
      // p     ==> false <==> not p
      else if (q instanceof FalsePred)
      {
        result = factory_.createNegPred(p);
      }
    }
    if (result == null)
    {
      result = factory_.createImpliesPred(p, q);
    }
    return result;
  }
}
