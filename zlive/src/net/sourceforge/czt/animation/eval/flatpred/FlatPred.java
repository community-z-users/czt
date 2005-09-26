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

import java.lang.reflect.Constructor;
import java.util.*;

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

  /** The list of arguments to this FlatPred.
      If the FlatPred corresponds to a function, the output is args[last].
   */
  protected /*@non_null@*/ ArrayList<ZRefName> args;

  /** The number of solutions that have been returned by nextEvaluation().
      This is -1 before startEvaluation() is called and 0 immediately
      after it has been called.
    */
  protected int solutionsReturned = -1;
  
  /** Get the mode that has been set for evaluation purposes. */
  //@ ensures \result == evalMode_;
  public /*@pure@*/ Mode getMode()
  { return evalMode_; }

  /** Get the environment that is being used during evaluation.
   *  @return Envir if known, else null. */
  public/*@pure@*/Envir getEnvir() {
    if (evalMode_ != null)
      return evalMode_.getEnvir();
    else
      return null;
  }

  /** Returns the free variables that appear in the predicate. */
  public Set<ZRefName> freeVars() {
    return new HashSet<ZRefName>(args);
  }

  /** Infer bounds for any integer variables.
   *  This analyzes the possible range of values of each integer
   *  variable used by this FlatPred, and reduces the range of values
   *  if possible.  This is a kind of static analysis commonly used
   *  in constraint solvers (bounds consistency).
   *  For example, if y already has the range 10..20,
   *  then the FlatPred x &lt; y would set the maximum value of x to 19.
   *  
   *  @param bnds  The database of lower and upper bounds for integer variables.
   *  @return      true iff the bnds database has been changed.
   *  <p>
   *  The default implementation infers nothing and returns false.
   *  </p>
   */
  public boolean inferBounds(Bounds bnds)
  {
    return false;
  }
  
  /** Choose the mode that this predicate could use in this environment.
      The result is null if no evaluation is possible.
      Otherwise, the resulting Mode object contains an updated
      environment (with any output variables added), plus various
      estimates about how expensive this predicate will be to execute.

      @return The Mode object, with statistics and an updated environment.
   */
  public abstract Mode chooseMode( /*@non_null@*/Envir env);

  /** Look up the environment to see which args are inputs. 
    @param env     The environment to lookup
    @return        The number of inputs.
    */
  protected BitSet getInputs(/*@non_null@*/Envir env)
  {
    BitSet inputs = new BitSet();
    for (int i=0; i<args.size(); i++) {
      if (env.isDefined(args.get(i))) {
        inputs.set(i);
      }
    }
    return inputs;
  }
  
  
  /** A default implementation of chooseMode.
      This returns mode IIIIII.. only.
      That is, all elements in the args list must be defined in env.
   */
  protected Mode modeAllDefined(/*@non_null@*/Envir env)
  {
    BitSet inputs = getInputs(env);
    double solutions = 0.0;
    if (inputs.cardinality() == args.size())
      solutions = 0.5;
    Mode m = null;
    if (solutions > 0.0)
      m = new Mode(env, inputs, solutions);
    return m;
  }

  
  
  /** A default implementation of chooseMode.
      This returns modes IIII... and III...O only.
      That is, all inputs to the function must be defined in env.
   */
  protected Mode modeFunction(/*@non_null@*/Envir env)
  {
    BitSet inputs = getInputs(env);
    double solutions = 0.0;
    if (inputs.cardinality() == args.size())
      solutions = 0.5;
    else if (inputs.cardinality() == args.size() - 1 
        && ! inputs.get(args.size()-1)) {
      solutions = 1.0;
      env = env.add(args.get(args.size()-1), null);
    }
    Mode m = null;
    if (solutions > 0.0)
      m = new Mode(env, inputs, solutions);
    return m;
  }
 
   /** A default implementation of chooseMode.
      For example, with 3 args, this returns modes III(0.5), 
      OII(1.0), IOI(1.0), IIO(1.0).
      That is, n-1 args must be defined in env.
   */
  protected Mode modeOneOutput(/*@non_null@*/Envir env)
  {
    BitSet inputs = getInputs(env);
    double solutions = 0.0;
    if (inputs.cardinality() == args.size())
      solutions = 0.5;
    else if (inputs.cardinality() == args.size() - 1) {
      solutions = 1.0;
      // add the output variable into the environment
      for (int i = 0; i < args.size(); i++) {
        if ( ! inputs.get(i))
          env = env.add(args.get(i), null);
      }
    }
    Mode m = null;
    if (solutions > 0.0)
      m = new Mode(env, inputs, solutions);
    return m;
  }

 /** Set the mode that will be used to evaluate this predicate.
      @param mode Must be one of the modes returned previously by chooseMode.
   */
  //@ ensures evalMode_ == mode;
  public void setMode( /*@non_null@*/ Mode mode)
  {
    evalMode_ = mode;
    solutionsReturned = -1;
  }

  //@ requires getMode() != null;
  public void startEvaluation()
  {
    solutionsReturned = 0;
  }

  /** Generates the next solution that satisfies this predicate.
      This must only be called after startEvaluation().
      @return true iff another solution has been found.
   */
  //@ requires getMode() != null;
  //@ requires solutionsReturned >= 0;
  public abstract boolean nextEvaluation();

  /** A default implementation of toString.
      This returns "FlatXXX(args[0], args[1], ...)".
      */
  public String toString() {
    StringBuffer result = new StringBuffer();
    String fullName = this.getClass().getName();
    int dotPos = fullName.lastIndexOf('.') + 1; // -1 becomes 0.
    result.append(fullName.substring(dotPos));
    result.append("(");
    for (Iterator<ZRefName> i = args.iterator(); i.hasNext(); ) {
      ZRefName name = i.next();
      result.append(name.toString());
      if (i.hasNext())
        result.append(",");
    }
    result.append(")");
    return result.toString();
  }


  ///////////////////////// Pred methods ///////////////////////

  /** Calls visitor.visitPred (preferably) or visitor.visitTerm.
      Subclasses that correspond to particular kinds of Pred
      should override this to call more specific visitXXX methods
      (and should call super to handle the remaining cases).
  */
  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatPredVisitor)
      return ((FlatPredVisitor)visitor).visitFlatPred(this);
    else
      return super.accept(visitor);
  }

  /** Returns the args of this FlatPred.
      The default implementation just returns args.
      Subclasses that have additional arguments should override this method.
  */
  public /*@non_null@*/ Object[] getChildren()
  {
     return args.toArray();
  }

  /** Creates a new FlatPred of the same type as this one.
      The default implementation uses reflection to call the
      FlatXXX(Object[] args) constructor of the subclass.
      Subtypes that need more specific initialisation could
      override this.
  */
  public /*@non_null@*/ Term create(/*@non_null@*/ Object[] newargs)
  {
    try {
      ArrayList<ZRefName> args = new ArrayList<ZRefName>(newargs.length);
      for (int i = 0; i < newargs.length; i++)
        args.set(i, (ZRefName)newargs[i]);
      Class[] paramTypes = {args.getClass()};
      Constructor cons = this.getClass().getConstructor(paramTypes);
      Object[] params = {args};
      return (Term)cons.newInstance(params);
    }
    catch (Exception e) {
      throw new IllegalArgumentException ("Bad arguments to create",e);
    }
  }
  
  /** Equality of an EvalSet with another EvalSet or Set. */
  public boolean equalsEvalSet(/*@non_null@*/EvalSet s1, Object s2) {
    Set elems1 = new HashSet();
    Iterator it = s1.members();
    while (it.hasNext()) {
      Object value = it.next();
      elems1.add(value);
    }
    Set elems2 = null;
    if (s2 instanceof Set)
      elems2 = (Set)s2;
    else if (s2 instanceof EvalSet) {
      elems2 = new HashSet();
      it = ((EvalSet)s2).members();
      while (it.hasNext()) {
        Object value = it.next();
        elems2.add(value);
      }
    } else {
      return false;
    }
    return elems1.equals(elems2);
  }
}
