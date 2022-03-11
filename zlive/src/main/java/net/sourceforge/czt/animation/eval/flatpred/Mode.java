/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import java.util.List;
import java.util.Set;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.PrintVisitor;

/** A Mode object contains information about one way of executing a FlatPred.
    It contains statistics about the number of solutions expected when
    the FlatPred is executed, plus an updated environment which contains
    any variables created by the FlatPred.

    @author marku
 */
public class Mode
{
  /*========= constants for mode results =============*/
  /** A constant for getSolutions().
   *  Means that one solution is expected.
   */
  public final static double ONE_SOLUTION = 1.0;

  /** A constant for getSolutions().
   *  Means that zero or one solutions are expected.
   */
  public final static double MAYBE_ONE_SOLUTION = 0.8;

  /** The expected number of solutions. */
  protected /*@spec_public@*/ double solutions_;
  //@ invariant solutions_ > 0.0;

  /** The environment before executing the FlatPred. */
  protected /*@spec_public@*/ Envir preEnvir_;

  /** The environment after executing the FlatPred. */
  protected /*@spec_public@*/ Envir postEnvir_;

  /** A copy of the arguments of this FlatPred.
   *  These are just saved for convenience, so that we
   *  can provide the isInput(int) method.
   */
  protected List<ZName> args_;

  /** The number of output variables. */
  protected int outputs_ = 0;

  protected FlatPred parent_;

  /** Constructor for Mode objects. */
  //@ requires solns > 0.0;
  public Mode(/*@non_null@*/FlatPred parent,
              /*@non_null@*/Envir preEnv,
              /*@non_null@*/List<ZName> args,
               double solns) {
    parent_ = parent;
    preEnvir_ = preEnv;
    postEnvir_ = preEnv;
    solutions_ = solns;
    args_ = args;
    for (ZName name : args) {
      if ( ! preEnvir_.isDefined(name)) {
        outputs_++;
        if ( ! postEnvir_.isDefinedSince(preEnvir_, name))
          postEnvir_ = postEnvir_.plus(name, null);
      }
    }
  }

  /** Returns the FlatPred that created this mode */
  public FlatPred getParent()
  {
    return parent_;
  }

  /** Is the given argument an input? */
  public /*@pure@*/ boolean isInput(ZName arg)
  {
    return preEnvir_.isDefined(arg)
      && ! postEnvir_.isDefinedSince(preEnvir_, arg);
  }

  /** A convenience version of isInput that takes the
   *  position of the variable in the FlatPred getArgs() list.
   */
  public /*@pure@*/ boolean isInput(int pos)
  {
    return isInput(args_.get(pos));
  }

  /** Is the given argument an output? */
  public /*@pure@*/ boolean isOutput(ZName arg)
  {
    return postEnvir_.isDefinedSince(preEnvir_, arg);
  }

  /** The estimated number of solutions that the FlatPred will produce.
      The result will always be positive.  It is an approximation of how many
      solutions the FlatPred is likely to generate in this mode.
      For example, 1.0 means exactly one solution is expected, 100 means
      that around 100 solutions are expected, and 0.5 means that 0 or 1
      solutions are expected.
  */
  //@ requires true;
  //@ ensures \result == solutions_;
  public /*@pure@*/ double getSolutions()
  { return solutions_; }

  /** Set the estimated number of solutions the FlatPred will produce.
   */
  //@ assignable solutions_;
  //@ ensures solutions_ = solns;
  public void setSolutions(double solns)
  { solutions_ = solns; }

  /** Get the input environment of this Mode. */
  //@ requires true;
  //@ ensures \result == preEnvir_;
  public /*@pure@*/ Envir getEnvir0()
  { return preEnvir_; }

  /** Get the environment that includes any output variables of FlatPred. */
  //@ requires true;
  //@ ensures \result == postEnvir_;
  public /*@pure@*/ Envir getEnvir()
  { return postEnvir_; }

  /** Gives the variables added to the environment by this mode. */
  public /*@pure@*/ Set<ZName> getOutputs()
  {
    return postEnvir_.definedSince(preEnvir_);
  }

  /** Gives the number of output variables. */
  public /*@pure@*/ int numOutputs()
  {
    return outputs_;
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("Mode{");
    PrintVisitor printVisitor =  new PrintVisitor(false);
    for (ZName name : postEnvir_.definedSince(preEnvir_)) {
      result.append(name.accept(printVisitor));
      result.append(" ");
    }
    result.append(solutions_);
    result.append("}");
    return result.toString();
  }

  /** Two modes are compatible if they have the same outputs.
   *  However, either side is allowed to have extra tmp* outputs.
   *
   *  TODO: check the correctness of this by checking that those
   *      extra tmp* outputs do not appear free outside that disjunct.
   *      Ideally, the constructor of the FlatOr should remove such names
   *      from the freevar set.  However, this is not easy to do, because
   *      it requires a more global view than the constructor has.
   *      
   *      Ideally, we should compare just the *free* variables
   *      of the two predicates.
   */
  public boolean compatible(/*@non_null@*/Mode other)
  {
    Set<ZName> leftOut = getOutputs();
    Set<ZName> rightOut = other.getOutputs();
    for (ZName out : leftOut) {
      if ( ! rightOut.contains(out) && ! ZLive.isNewName(out)) {
        return false;
      }
    }
    for (ZName out : rightOut) {
      if ( ! leftOut.contains(out) && ! ZLive.isNewName(out)) {
        return false;
      }
    }
    return true;
  }
}
