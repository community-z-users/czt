/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

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
import java.util.ArrayList;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.PredImpl;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatPred is the base class of the flattened predicates used in ZLive.
    Each flattened predicate can be evaluated in one or more different
    'modes' (a mode is defined by a set of input variables and a set
    of output variables).  Each FlatPred provides facilities for choosing
    a particular mode, given environment information about what input
    variables are available, and for generating all solutions
    using that mode.
    Note that each FlatPred has at most one mode in a given environment.
    Environments are updated non-destructively.
    <p>
    <strong>Design Rationale:</strong>
    The natural representation of the data inside each kind of
    FlatPred is quite different to the normal CZT AST classes,
    which means that the standard CZT visitors and utilities would
    not automatically work on FlatPred classes.
    However, for backwards compatibility, the FlatPred classes
    implement the Pred interface, and generate the appropriate children
    on the fly, so that they seem to be standard Z AST objects.  For example,
    this allows the usual print visitors to display the FlatPred objects.
    <p>
    The mode selection uses a stateless interface, where the chosen mode
    information is returned in a separate object rather than changing
    the internal state of the FlatPred.  This enables different
    input environments to be tried and the corresponding modes stored and
    compared, which gives more flexibility in the searching algorithms
    that use modes.
 */
public abstract class FlatPred extends PredImpl
{
  /** The mode that will be used during evaluation.
      This is usually set by an explicit call to setMode().
  */
  protected /*@spec_public@*/ Mode evalMode_;

  /** Get the mode that has been set for evaluation purposes. */
  //@ requires true;
  //@ ensures \result == evalMode_;
  public /*@pure@*/ Mode getMode()
  { return evalMode_; }

  /** Choose the mode that this predicate could use in this environment.
      The result is null if no evaluation is possible.
      Otherwise, the resulting Mode object contains an updated
      environment (with any output variables added), plus various
      estimates about how expensive this predicate will be to execute.

      @return The Mode object, with statistics and an updated environment.
   */
  public abstract Mode chooseMode( /*@non_null@*/Envir env);

  /** Set the mode that will be used to evaluate this predicate.
      @param mode Must be one of the modes returned previously by chooseMode.
   */
  //@ ensures evalMode_ == mode;
  public void setMode( /*@non_null@*/ Mode mode)
  { evalMode_ = mode; }

  //@ requires getMode() != null;
  public abstract void startEvaluation();

  /** Generates the next solution that satisfies this predicate.
      This must only be called after startEvaluation().
      @return true iff another solution has been found.
   */
  //@ requires getMode() != null;
  public abstract boolean nextEvaluation();


  ///////////////////////// Pred methods ///////////////////////

  /** Calls visitor.visitPred (preferably) or visitor.visitTerm.
      Subclasses that correspond to particular kinds of Pred
      should override this to call more specific visitXXX methods
      (and should call super to handle the remaining cases).
  */
  public Object accept(Visitor visitor)
  {
    return super.accept(visitor);
  }

  /** Returns the subtrees of this FlatPred.
      Subclasses should implement this to emulate one of the Pred subtypes.
      For example, a FlatPred whose semantics is similar to a MemPred
      should return an array of children similar to what a MemPred
      object would return.
  */
  public abstract /*@non_null@*/ Object[] getChildren();

  /** Creates a new FlatPred of the same type as this one.
      Subtypes should implement this to set their internal
      data based on the values in args.
  */
  public abstract /*@non_null@*/ Term create(Object[] args);
}
