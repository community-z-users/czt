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
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZSchText;
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

  public Pred falsePred()
  {
    return factory_.createFalsePred();
  }

  public Pred checkNeg(Pred pred)
  {
    Pred result = pred;
    if (isApplyingTransformer() && pred instanceof NegPred)
    {
      Pred innerPred = ((NegPred)pred).getPred();
      // \lnot (\lnot P) = P (DOUBLE-NEGATION)
      if (innerPred instanceof NegPred)
      {
        // in case of more than 1 double negation
        result = checkNeg(((NegPred)pred).getPred());
      }
      // \lnot false = true (UNIT-FALSE)
      else if(innerPred instanceof FalsePred)
      {
        result = truePred();
      }
      // \lnot true = false (UNIT-TRUE)
      else if (innerPred instanceof TruePred)
      {
        result = falsePred();
      }
      // \lnot (P \land Q) = \lnot P \lor \lnot Q (DEMORGAN-AND)
      else if (innerPred instanceof AndPred)
      {
        AndPred ai = (AndPred)innerPred;
        // negate each side and then push negations inward
        Pred lhs = checkNeg(factory_.createNegPred(ai.getLeftPred()));
        Pred rhs = checkNeg(factory_.createNegPred(ai.getRightPred()));
        // or the result
        result = orPred(lhs, rhs); // don't checkNeg here - orPred does it
      }
      // \lnot (P \lor Q) = \lnot P \land \lnot Q (DEMORGAN-OR)
      else if (innerPred instanceof OrPred)
      {
        OrPred oi = (OrPred)innerPred;
        // negate each side and then push negations inward
        Pred lhs = checkNeg(factory_.createNegPred(oi.getLeftPred()));
        Pred rhs = checkNeg(factory_.createNegPred(oi.getRightPred()));
        // and the result
        result = andPred(lhs, rhs); // don't checkNeg here - andPred does it
      }
      // \lnot (P \implies Q) = P \land \lnot Q (DEMORGAN-IMP)
      else if (innerPred instanceof ImpliesPred)
      {
        ImpliesPred ip = (ImpliesPred)innerPred;
        Pred rhs = checkNeg(factory_.createNegPred(ip.getRightPred()));
        result = andPred(ip.getLeftPred(), rhs); // don't checkNeg here - andPred does it
      }
      // DON'T APPLY QUANTIFIER DEMORGAN-LAWS
      //else if (innerPred instanceof ExistsPred || innerPred instanceof ForallPred)
    }
    assert result != null;
    return result;
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
      // P \land false = false \land P = false (AND-ZERO)
      if (lhs instanceof FalsePred || rhs instanceof FalsePred)
      {
        result = falsePred();
      }
      // true \land RHS = RHS (AND-UNIT-R)
      else if(lhs instanceof TruePred)
      {
        result = rhs;
      }
      // LHS \land true = LHS (AND-UNIT-L)
      else if (rhs instanceof TruePred)
      {
        result = lhs;
      }
      // LHS \land LHS = LHS (AND-IDEMPOTENT)
      else if (lhs.equals(rhs))
      {
        result = checkNeg(lhs);
      }
      // \lnot P \land P  = P \land \lnot P = false (AND-CONTRADICTION)
      else if ((lhs instanceof NegPred && ((NegPred)lhs).getPred().equals(rhs)) ||
               (rhs instanceof NegPred && ((NegPred)rhs).getPred().equals(lhs)))
      {
        result = falsePred();
      }
      // These next two laws could be greatly simplified
      // we leave them as such for clarity at first.
      //
      // (\lnot P \lor Q) \land P = Q \land P (AND-ABSORPTION-L)
      else if (lhs instanceof OrPred)
      {
        OrPred olhs = (OrPred)lhs;
        // (\lnot P \lor Q) \land P -> return LHS=Q
        if (olhs.getLeftPred() instanceof NegPred &&
            ((NegPred)olhs.getLeftPred()).equals(rhs))
        {
          lhs = olhs.getRightPred();
        }
        // (Q \lor \lnot P) \land P -> return LHS=Q
        else if (olhs.getRightPred() instanceof NegPred &&
            ((NegPred)olhs.getRightPred()).equals(rhs))
        {
          lhs = olhs.getLeftPred();
        }
        // let result as null: will create LHS \land RHS
      }
      // P \land (\lnot P \lor Q) = P \land Q (AND-ABSORPTION-R)
      else if (rhs instanceof OrPred)
      {
        OrPred rlhs = (OrPred)rhs;
        // P \land (\lnot P \lor Q) -> return RHS=Q
        if (rlhs.getLeftPred() instanceof NegPred &&
            ((NegPred)rlhs.getLeftPred()).equals(lhs))
        {
          rhs = rlhs.getRightPred();
        }
        // P \land (Q \lor \lnot P) -> return RHS=Q
        else if (rlhs.getRightPred() instanceof NegPred &&
            ((NegPred)rlhs.getRightPred()).equals(lhs))
        {
          rhs = rlhs.getLeftPred();
        }
        // let result as null: will create LHS \land RHS
      }
      // at last check if could push negation inwards
      lhs = checkNeg(lhs);
      rhs = checkNeg(rhs);
    }
    if (result == null)
    {
      //assert lhs != null && rhs != null;
      result = checkNeg(factory_.createAndPred(lhs, rhs, And.Wedge));
    }
    assert result != null;
    return result;
  }

  public Pred orPred(Pred lhs, Pred rhs)
  {
    assert lhs != null && rhs != null : "Invalid OrPred request!";
    Pred result = null;
    if (isApplyingTransformer())
    {
      // true or P = P or true = true (OR-ZERO)
      if (lhs instanceof TruePred || rhs instanceof TruePred)
      {
        result = truePred();
      }
      // false or P = P (OR-UNIT-R)
      else if (lhs instanceof FalsePred)
      {
        result = rhs;
      }
      // P or false = P (OR-UNIT-L)
      else if (rhs instanceof FalsePred)
      {
        result = lhs;
      }
      // P or P = P (OR-IDEMPOTENT)
      else if (lhs.equals(rhs))
      {
        result = lhs;
      }
      // \lnot P \lor P  = P \lor \lnot P = true (OR-EXCLUDED-MIDDLE)
      else if ((lhs instanceof NegPred && ((NegPred)lhs).getPred().equals(rhs)) ||
               (rhs instanceof NegPred && ((NegPred)rhs).getPred().equals(lhs)))
      {
        result = truePred();
      }
      // These next two laws could be greatly simplified
      // we leave them as such for clarity at first.
      //
      // (\lnot P \land Q) \lor P = Q \lor P (OR-ABSORPTION-L)
      else if (lhs instanceof AndPred)
      {
        AndPred alhs = (AndPred)lhs;
        // (\lnot P \land Q) \lor P -> return LHS=Q
        if (alhs.getLeftPred() instanceof NegPred &&
            ((NegPred)alhs.getLeftPred()).equals(rhs))
        {
          lhs = alhs.getRightPred();
        }
        // (Q \land \lnot P) \lor P -> return LHS=Q
        else if (alhs.getRightPred() instanceof NegPred &&
            ((NegPred)alhs.getRightPred()).equals(rhs))
        {
          lhs = alhs.getLeftPred();
        }
        // let result as null: will create LHS \land RHS
      }
      // P \lor (\lnot P \land Q) = P \lor Q (AND-ABSORPTION-R)
      else if (rhs instanceof AndPred)
      {
        AndPred rlhs = (AndPred)rhs;
        // P \lor (\lnot P \land Q) -> return RHS=Q
        if (rlhs.getLeftPred() instanceof NegPred &&
            ((NegPred)rlhs.getLeftPred()).equals(lhs))
        {
          rhs = rlhs.getRightPred();
        }
        // P \lor (Q \land \lnot P) -> return RHS=Q
        else if (rlhs.getRightPred() instanceof NegPred &&
            ((NegPred)rlhs.getRightPred()).equals(lhs))
        {
          rhs = rlhs.getLeftPred();
        }
        // let result as null: will create LHS \lor RHS
      }
      // at last check if could push negation inwards
      lhs = checkNeg(lhs);
      rhs = checkNeg(rhs);
    }
    if (result == null)
    {
      assert lhs != null && rhs != null;
      result = checkNeg(factory_.createOrPred(lhs, rhs));
    }
    assert result != null;
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
    assert result != null;
    return result;
  }


  /**
   * Creates a ForAllPred with the given declarations and predicate.
   * That is, "\forall decl @ pred". We apply the simple zero-law:
   * <ul>
   *  <li>\forall D @ true \iff true </li>
   *  <li>\forall D | false @ true \iff true </li>
   * </ul>
   * Even if D is false, this is the right transformation as anything implies true.
   * @param decl
   * @param pred
   * @return
   */
  public Pred forAllPred(ZDeclList decl, Pred pred)
  {
    assert decl != null : "Invalid ForAllPred request!";
    return forAllPred(factory_.createZSchText(decl, truePred()), pred);
  }

  public Pred forAllPred(ZSchText zSchText, Pred pred)
  {
    assert zSchText != null && pred != null : "Invalid ForAllPred request!";
    Pred result = null;
    if (isApplyingTransformer())
    {
      pred = checkNeg(pred);
      zSchText.setPred(checkNeg(zSchText.getPred() != null ? zSchText.getPred() : truePred()));//If null, just sets null.
      // (\forall D | P @ true) = (\forall D | false @ Q) = true
      if (pred instanceof TruePred || zSchText.getPred() instanceof FalsePred)
      {
        result = truePred();
      }
    }
    if (result == null)
    {
      assert /*pred != null &&*/ zSchText.getPred() != null;
      result = checkNeg(factory_.createForallPred(zSchText, pred));
    }
    assert result != null;
    return result;
  }

  public Pred existsPred(ZDeclList decl, Pred pred)
  {
    assert decl != null : "Invalid ExistPred request!";
    return existsPred(factory_.createZSchText(decl, truePred()), pred);
  }

  public Pred existsPred(ZSchText zSchText, Pred pred)
  {
    assert zSchText != null && pred != null : "Invalid ExistPred request!";
    Pred result = null;
    if (isApplyingTransformer())
    {
      pred = checkNeg(pred);
      zSchText.setPred(checkNeg(zSchText.getPred() != null ? zSchText.getPred() : truePred()));//If null, just sets null.
      // (\exists D | P @ false) = (\exists D | false @ Q) = false
      if (pred instanceof FalsePred || zSchText.getPred() instanceof FalsePred)
      {
        result = falsePred();
      }
    }
    if (result == null)
    {
      assert /*pred != null &&*/ zSchText.getPred() != null;
      result = checkNeg(factory_.createExistsPred(zSchText, pred));
    }
    assert result != null;
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
   * @param lhs
   * @param rhs
   * @return
   */
  public Pred impliesPred(Pred lhs, Pred rhs)
  {
    assert lhs != null && rhs != null : "Invalid ImpliesPred request!";
    Pred result = null;
    if (isApplyingTransformer())
    {
      lhs = checkNeg(lhs);
      rhs = checkNeg(rhs);
      // true     ==> q     <==> q                  (IMP-UNIT-R)
      // p        ==> true  <==> true (which is q)  (IMP-ZERO-R)
      // \lnot p  ==> P     <==> P (which is q)     (IMP-CROSSOVER-R)
      if (lhs instanceof TruePred || rhs instanceof TruePred ||
          (lhs instanceof NegPred && ((NegPred)lhs).getPred().equals(rhs)))
      {
        result = rhs;
      }
      // false ==> q     <==> true              (IMP-FALSE-ANTC)
      // P     ==> P     <==> true              (IMP-REFLECT)
      else if ((lhs instanceof FalsePred) || lhs.equals(rhs))
      {
        result = truePred();
      }
      // p     ==> false <==> not p             (IMP-FALSE-CONSQ)
      // P     ==> not P <==> not P             (IMP-CROSSOVER-L)
      else if (rhs instanceof FalsePred || (rhs instanceof NegPred && ((NegPred)rhs).getPred().equals(lhs)))
      {
        result = factory_.createNegPred(lhs);
      }
      // R \implies P \land Q  <==> (R \implies P) \land (R \imples Q) IMP-CASE-SPLIT-CONSQ3
      // (P \lor Q) \implies R <==> (P \imples R) \lor (Q \implies R) IMP-CASE-SPLIT-ANTC
      else if (rhs instanceof AndPred || lhs instanceof OrPred)
      {
        // do nothing on this one for now.
      }
    }
    if (result == null)
    {
     // assert lhs != null && rhs != null;
      result = checkNeg(factory_.createImpliesPred(lhs, rhs));
    }
    assert result != null;
    return result;
  }
}
