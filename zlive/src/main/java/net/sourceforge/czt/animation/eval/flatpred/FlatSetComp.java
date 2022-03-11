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

import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatSetCompVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.animation.eval.result.SetComp;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;

/**
* @author Mark Utting
*
* FlatSetComp(decls,pred,expr) implements {decls|pred@expr}
*/
public class FlatSetComp extends FlatPred
{
  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** This FlatPredList is used to evaluate ALL members of the set. */
  protected FlatPredList predsAll_;

  /** The fresh ZName which will be bound to a member of the set. */
  protected ZName resultName_;

  /** FlatSetComp(D,P,E,S) implements {D|P@E} = S.
   *
   * @param decls   A list of Decl objects (ConstDecl and VarDecl only).
   * @param pred    The predicate that filters the declarations.
   * @param result  The expression returned by the set.
   * @param set     The variable that the whole set will be equated to.
   */
  public FlatSetComp(/*@non_null@*/ZLive zlive,
		     /*@non_null@*/ZSchText stext,
		     /*@non_null@*/Expr result,
		     /*@non_null@*/ZName set)
  {
    predsAll_ = new FlatPredList(zlive);
    predsAll_.addExistsSchText(stext);
    resultName_ = predsAll_.addExpr(result);

    args_ = new ArrayList<ZName>(predsAll_.freeVars());
    // Note the pathological case where set is already in args:
    //       For example:   s = {x:\nat | x < #s @ x}
    // chooseMode handles this correctly, because modeFunction requires
    // args_[0..size-2] to be inputs, which includes set in this case.
    args_.add(set);
    solutionsReturned_ = -1;
  }

  /** This does local bounds inference.
   *  So bounds information flows into the set, but only
   *  information about the whole set flows out.
   */
  public boolean inferBounds(Bounds bnds)
  {
    if (bounds_ == null)
      bounds_ = new Bounds(bnds);
    bounds_.startAnalysis(bnds);
    boolean result = predsAll_.inferBounds(bounds_);
    bounds_.endAnalysis();

    String name = getLastArg().toString();
    // TODO: it would be nice to get a better size estimate here,
    // but we do not know the values of the free variables yet,
    // so it is difficult to use chooseMode on predsAll_.
    // TODO: set them all to null and run chooseMode?
    FuzzySet fuzzy = new FuzzySet(name, EvalSet.UNKNOWN_SIZE, null);
    fuzzy.setLower(bounds_.getLower(resultName_));
    fuzzy.setUpper(bounds_.getUpper(resultName_));

    // now tell the outer Bounds object a summary of what we know.
    result |= bnds.setEvalSet(getLastArg(), fuzzy);
    return result;
  }

  /** Like other Flat*Set* objects, this acts as a function:
   *  the free variables of the set are the inputs and the
   *  resulting EvalSet object is the output.
   *  The number of solutions is always 1, since this just
   *  defines the whole set, rather than iterating through it.
   */
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    LOG.entering("FlatSetComp","chooseMode",env);
    LOG.fine("args = "+args_+" freevars="+this.freeVars_);
    assert bounds_ != null; // inferBounds should have been called.
    Mode m = modeFunction(env);
    // bind (set |-> fuzzy), so that size estimates work better.
    /* TODO: it would be nice to add more precise bounds
     *  information here, since we now know the free vars
     *  of this set.  But we cannot add a fuzzy set to the
     *  environment, because it will be mistaken for the actual
     *  solution.  Is there a nice way of adding it to bounds
     *  but still leaving chooseMode to be side-effect-free?

    Mode all = predsAll_.chooseMode(env);
    if (m != null && all != null) {
      FuzzySet fuzzy = new FuzzySet(getLastArg().toString(),
                              all.getSolutions(), null);
      BigInteger lo = bounds_.getLower(resultName_);
      if (lo != null)
        fuzzy.setLower(lo);
      BigInteger up = bounds_.getUpper(resultName_);
      if (up != null)
        fuzzy.setUpper(up);
      m.getEnvir().setValue(getLastArg(), fuzzy);
    }
    */
    LOG.exiting("FlatSetComp","chooseMode",m);
    return m;
  }

  /** Does the actual evaluation.
   *  In fact, in output mode this is lazy -- it just assigns
   *  a SetComp object to the output variable, so that the members of
   *  the set can be evaluated (and cached) only when needed.
   *  This is the same as lazy evaluation in functional languages.
   */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    boolean result = false;
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      ZName setName = getLastArg();
      SetComp set = new SetComp(predsAll_, resultName_,
                                evalMode_.getEnvir0().deepCopy(), bounds_);
      if (evalMode_.isInput(args_.size()-1)) {
        Expr otherSet = evalMode_.getEnvir().lookup(setName);
        result = set.equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(setName, set);
        result = true;
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printQuant(printLastArg() + " = {",
        predsAll_.toString(),
        printName(resultName_),
        "}");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatSetCompVisitor)
      return ((FlatSetCompVisitor<R>) visitor).visitFlatSetComp(this);
    else
      return super.accept(visitor);
  }
}
