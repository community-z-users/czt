/**
Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.*;
import java.math.*;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.TermAImpl;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;

/**
* @author Mark Utting
*
* FlatSetComp(decls,pred,expr) implements {decls|pred@expr}
*/
public class FlatSetComp
  extends FlatPred
  implements EvalSet
{
  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** This FlatPredList is used to evaluate ALL members of the set. */
  protected FlatPredList predsAll_;

  /** This FlatPredList is used to check membership of ONE given value.
      Its first entry is resultNNN=value, where resultNNN is a fresh
      ZRefName (see resultName) and value is initially unknown, but will
      be set within isMember before this FlatPredList is evaluated.
  */
  protected FlatPredList predsOne_;

  /** The fresh ZRefName which will be bound to a member of the set. */
  protected ZRefName resultName_;

  /** The set of member values in the resulting set. */
  protected Set<Expr> knownMembers_;
  
  /** FlatSetComp(D,P,E,S) implements {D|P@E} = S.
   * 
   * @param decls   A list of Decl objects (ConstDecl and VarDecl only).
   * @param pred    The predicate that filters the declarations.
   * @param result  The expression returned by the set.
   * @param set     The variable that the whole set will be equated to.
   */
  public FlatSetComp(/*@non_null@*/ZLive zlive, 
		       /*@non_null@*/List<Decl> decls, 
		       Pred pred, 
		       /*@non_null@*/Expr result,
		       /*@non_null@*/ZRefName set)
  {
    predsAll_ = new FlatPredList(zlive);
    predsOne_ = new FlatPredList(zlive);
    resultName_ = zlive.createNewName();
    // TODO: not needed now: predsOne_.add(new FlatConst(resultName_,null));
    for (Iterator i = decls.iterator(); i.hasNext(); ) {
      Decl decl = (Decl)i.next();
      predsAll_.addDecl(decl);
      predsOne_.addDecl(decl);
    }
    if (pred != null) {
      predsAll_.addPred(pred);
      predsOne_.addPred(pred);
    }
    // Now add 'resultName = result'.
    RefExpr resultExpr = zlive.getFactory().createRefExpr(resultName_);
    Pred eq = zlive.getFactory().createEquality(resultExpr, result);
    predsAll_.addPred(eq);
    predsOne_.addPred(eq);

    // Calculate free vars of preds_.
    args = new ArrayList<ZRefName>(predsAll_.freeVars());
    args.add(set);  // TODO: could set already be in args?
    solutionsReturned = -1;
    knownMembers_ = null;
  }

  public boolean inferBounds(Bounds bnds)
  {
    // we infer bounds for both copies of the PredList.
    // They should be identical.
    boolean changeAll = predsAll_.inferBounds(bnds);
    boolean changeOne = predsOne_.inferBounds(bnds);
    assert changeAll == changeOne;
    changeAll |= bnds.setEvalSet(args.get(args.size()-1), this);
    bounds_ = bnds;
    return changeAll;
  }

  public BigInteger getLower()
  {
    if (bounds_ == null)
      return null;
    else
      return bounds_.getLower(resultName_);
  }

  public BigInteger getUpper()
  {
    if (bounds_ == null)
      return null;
    else
      return bounds_.getUpper(resultName_);
  }

  /** Returns null for now -- because it is quite complex to calculate
   *  maximum size of a set comprehension.
   *  
   *  TODO: estimate maximum size.
   */
  public BigInteger maxSize()
  {
	return null;
  }

  /** Like other Flat*Set* objects, this acts as a function:
      the free variables of the set are the inputs and the
      resulting EvalSet object is the output.
  */
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    LOG.entering("FlatSetComp","chooseMode",env);
    LOG.fine("args = "+args+" freevars="+this.freeVars_);
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue(args.get(args.size()-1), this);
    LOG.exiting("FlatSetComp","chooseMode",m);
    return m;
  }
  
  /** Estimate the size of the set. 
   *  This must only be called after setMode().
   */
  public double estSize(Envir env)
  {
    double est = EvalSet.UNKNOWN_SIZE;
    Mode m = predsAll_.chooseMode(env);
    if (m != null)
      est = m.getSolutions();
    return est;
  }

  /** Estimate the size of the set. */
  public double estSize()
  {
    assert(evalMode_ != null);
    // TODO: should use the ORIGINAL env here, not this one (which has 'set' added).
   return estSize(evalMode_.getEnvir());
  }

  /** TODO: try and get a better size estimate by equating
   *  elem to the result of the set before estimating its size?
   */
  public double estSubsetSize(Envir env, ZRefName elem)
  {
    return estSize(env);
  }
  
  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *  
  *  TODO: generate the members lazily, as requested by the iterator.
  *
  * @return an Iterator object which returns each member of the set.
  */
  public Iterator<Expr> members()
  {
    if (knownMembers_ == null) {
      // generate all members.
      // TODO: use the ORIGINAL env, not this one which has 'set' added.
      // TODO: we could generate the members lazily?
      Envir env0 = evalMode_.getEnvir();
      Mode m = predsAll_.chooseMode(env0);
      if (m == null)
        throw new EvalException("Cannot generate members of SetComp: " + this);
      knownMembers_ = new HashSet<Expr>();
      predsAll_.setMode(m);
      predsAll_.startEvaluation();
      Envir env = predsAll_.getOutputEnvir();
      while (predsAll_.nextEvaluation())
        knownMembers_.add(env.lookup(resultName_));
    }
    return knownMembers_.iterator();
  }

  /** TODO: see if we can use bounds information about element
   *  to reduce the size of the subset that we return?
   */
  public Iterator<Expr> subsetMembers(ZRefName element)
  {
    return members();
  }

  /** Does the actual evaluation.
   *  In fact, in output mode this is lazy -- it just assigns
   *  itself to the output variable, so that the members of
   *  the set can be evaluated (and cached) only when needed.
   *  This is the same as lazy evaluation in functional languages.
   */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    boolean result = false;
    knownMembers_ = null; // force members to be recalculated
    ZRefName set = args.get(args.size()-1);
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(args.size()-1)) {
        Expr otherSet = evalMode_.getEnvir().lookup(set);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(set, this);
        result = true;
      }
    }
    return result;
  }

  /** Tests for membership of the set.
  * @param e  The fully evaluated expression.
  * @return   true iff e is a member of the set.
  */
  //@ requires evalMode_ != null;
  public boolean isMember(Expr e)
  {
    assert(evalMode_ != null);
    Envir env = evalMode_.getEnvir();
    // Add the expected answer to the environment.
    // This allows the predicates inside the set to CHECK the result
    // rather than generating all possible results.
    env = env.add(resultName_, e);
    Mode m = predsOne_.chooseMode(env);
    if (m == null)
      throw new EvalException("Cannot even test member of SetComp: " + this);
    predsOne_.setMode(m);
    predsOne_.startEvaluation();
    return predsOne_.nextEvaluation();
  }

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatSetCompVisitor) {
      FlatSetCompVisitor flatVisitor = (FlatSetCompVisitor) visitor;
      return flatVisitor.visitFlatSetComp(this);
    }
    return super.accept(visitor);
  }

  /** True iff two EvalSets contain the same elements. */
  public boolean equals(Object otherSet) {
    return equalsEvalSet(this,otherSet);
  }
  
  /** @czt.todo Change this to a printCode method. */
  public String toString() {
    return "{ " + predsAll_.toString() + " @ " + resultName_ + " } = " + args.get(args.size()-1);
  }
}
