/**
Copyright (C) 2004 Mark Utting
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
  protected Factory factory_ = new Factory();
  public final double DEFAULT_SIZE = 1000000.0;

  /** This FlatPredList is used to evaluate ALL members of the set. */
  protected FlatPredList predsAll_;

  /** This FlatPredList is used to check membership of ONE given value.
      Its first entry is resultNNN=value, where resultNNN is a fresh
      RefName (see resultName) and value is initially unknown, but will
      be set within isMember before this FlatPredList is evaluated.
  */
  protected FlatPredList predsOne_;

  /** The fresh RefName which will be bound to a member of the set. */
  protected RefName resultName_;

  /** The set of free variables of this set. */
  protected Set freevars_;
  
  /** The set of member values in the resulting set. */
  protected Set knownMembers_;
  
  /** FlatSetComp(D,P,E,S) implements {D|P@E} = S.
   * 
   * @param decls   A list of Decl objects (ConstDecl and VarDecl only).
   * @param pred    The predicate that filters the declarations.
   * @param result  The expression returned by the set.
   * @param set     The variable that the whole set will be equated to.
   */
  public FlatSetComp(/*@non_null@*/ZLive zlive, 
		       /*@non_null@*/List/*<Decl>*/ decls, 
		       Pred pred, 
		       /*@non_null@*/Expr result,
		       /*@non_null@*/RefName set)
  {
    predsAll_ = new FlatPredList(zlive);
    predsOne_ = new FlatPredList(zlive);
    resultName_ = zlive.createNewName();
    predsOne_.add(new FlatConst(resultName_,null));
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
    Pred eq = factory_.createEquality(factory_.createRefExpr(resultName_), result);
    predsAll_.addPred(eq);
    predsOne_.addPred(eq);

    // Calculate free vars of preds_.
    freevars_ = predsAll_.freeVars();
    args = new ArrayList(freevars_);
    args.add(set);
    solutionsReturned = -1;
    knownMembers_ = null;
    System.out.println("DEBUG: FLATSETCOMP HAS SIZE "+predsAll_.size()+" "+predsOne_.size());
  }

  /** Like other Flat*Set* objects, this acts as a function:
      the free variables of the set are the inputs and the
      resulting EvalSet object is the output.
  */
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue((RefName)args.get(args.size()-1), this);
    return m;
  }
  
  /** Estimate the size of the set. 
   */
  public double estSize()
  {
    assert(evalMode_ != null);
    double est = 1000000.0;
    Mode m = predsAll_.chooseMode(evalMode_.getEnvir());
    if (m != null)
      est = m.getSolutions();
    return est;
  }

  /** A list of all the free variables that this set depends upon.
  * @return The free variables.
  */
  public Set/*<RefName>*/ freeVars()
  {
    return freevars_;
  }

  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *
  * @return an Iterator object which returns each member of the set.
  */
  public Iterator members()
  {
    if (knownMembers_ == null) {
      // generate all members.
      Envir env0 = evalMode_.getEnvir();
      Mode m = predsAll_.chooseMode(env0);
      if (m == null)
        throw new EvalException("Cannot generate members of SetComp: " + this);
      knownMembers_ = new HashSet();
      predsAll_.startEvaluation(m, env0);
      Envir env = m.getEnvir();
      while (predsAll_.nextEvaluation())
        knownMembers_.add(env.lookup(resultName_));
    }
    return knownMembers_.iterator();
  }

  public void startEvaluation() {
    super.startEvaluation();
    knownMembers_ = null;
  }
  
  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    assert evalMode_.isInput(0);
    assert evalMode_.isInput(1);
    boolean result = false;
    RefName set = (RefName)args.get(args.size()-1);
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
    Envir env0 = evalMode_.getEnvir();
    env0.setValue(resultName_, e);
    Mode m = predsOne_.chooseMode(env0);
    if (m == null)
      throw new EvalException("Cannot even test member of SetComp: " + this);
    predsOne_.startEvaluation(m, env0);
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
    if (otherSet instanceof EvalSet)
      return equalsEvalSet(this,(EvalSet)otherSet);
    else
      return false;
  }
}
