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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatPredVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.PrintVisitor;

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
public abstract class FlatPred
{
  protected static final String INDENT = "  ";
  
  protected static final Logger LOG =
    Logger.getLogger("net.sourceforge.czt.animation.eval");

  /** Records the free variables used within this predicate.
   *  This is calculated and cached by the freeVars() method.
   */
  protected Set<ZName> freeVars_;

  /** The mode that will be used during evaluation.
   *  This is usually set by an explicit call to setMode().
   */
  protected/*@spec_public@*/Mode evalMode_;

  /** The list of arguments to this FlatPred.
   *  If the FlatPred corresponds to a function, the output is
   *  the last entry in args.
   *  Note that it is permissible for args_ to contain the same
   *  name more than once.  For example, a*a=b gives FlatMult(a,a,b),
   *  which has args_=[a,a,b].
   */
  protected/*@non_null@*/ArrayList<ZName> args_;

  /** The number of solutions that have been returned by nextEvaluation().
   *  This is -1 before startEvaluation() is called and 0 immediately
   *  after it has been called.
   */
  protected int solutionsReturned_ = -1;

  /** A non-unicode print visitor used for debug and toString messages. */
  protected static PrintVisitor printer_ = new PrintVisitor(false);

  /** Default constructor for subclasses to call. */
  protected FlatPred()
  {
    args_ = new ArrayList<ZName>();
  }

  /** Get the list of variables that this predicate directly
   *  depends upon.  This usually contains the same variables
   *  as the freeVars set, but this list may contain duplicates.
   *  This should be treated as a read-only list.
   */
  public List<ZName> getArgs()
  {
    return args_;
  }

  /** Get the variable at the end of getArgs().
   *  This is usually the output' of this FlatPred.
   */
  public ZName getLastArg()
  {
    List<ZName> args = getArgs();
    return args.get(args.size() - 1);
  }

  /** Get the mode that has been set for evaluation purposes. */
  //@ ensures \result == evalMode_;
  public/*@pure@*/Mode getMode()
  {
    return evalMode_;
  }

  /** Get the output environment of the evaluation.
   *  @return Envir if known, else null.
   */
  public/*@pure@*/Envir getEnvir()
  {
    if (evalMode_ != null)
      return evalMode_.getEnvir();
    else
      return null;
  }

  /** Returns the free variables that appear in the predicate.
   *  The default implementation returns all the variables in args.
   */
  public Set<ZName> freeVars()
  {
    if (freeVars_ == null) {
      freeVars_ = new HashSet<ZName>(args_);
    }
    return freeVars_;
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

  /** A default implementation of chooseMode.
   This returns mode IIIIII.. only.
   That is, all elements in the args list must be defined in env.
   */
  protected Mode modeAllDefined(/*@non_null@*/Envir env)
  {
    Mode result = new Mode(this, env, getArgs(), Mode.MAYBE_ONE_SOLUTION);
    if (result.numOutputs() == 0)
      return result;
    else
      return null;
  }

  /** A default implementation of chooseMode.
   *  This returns modes IIII... and III...O only.
   *  That is, all inputs to the function must be defined in env.
   */
  protected Mode modeFunction(/*@non_null@*/Envir env)
  {
    Mode result = new Mode(this, env, getArgs(), Mode.ONE_SOLUTION);
    if (result.numOutputs() == 0)
      result.setSolutions(Mode.MAYBE_ONE_SOLUTION);
    else if (result.numOutputs() != 1
        || ! result.isOutput(getLastArg()))
      result = null;
    return result;
  }

  /** A default implementation of chooseMode.
   *  For example, with 3 args, this returns modes III(0.5),
   *  OII(1.0), IOI(1.0), IIO(1.0).
   *  That is, n-1 args must be defined in env.
   */
  protected Mode modeOneOutput(/*@non_null@*/Envir env)
  {
    Mode result = new Mode(this, env, getArgs(), 0.0);
    if (result.numOutputs() == 0)
      result.setSolutions(Mode.MAYBE_ONE_SOLUTION);
    else if (result.numOutputs() == 1)
      result.setSolutions(Mode.ONE_SOLUTION);
    else
      result = null;
    return result;
  }

  /** A default implementation of chooseMode.
   *  Useful when the last argument is a collection (tuple/binding)
   *  that contains all the other arguments.
   */
  public Mode modeCollection(Envir env)
  {
    Mode result = modeFunction(env);
    if (result == null && env.isDefined(getLastArg())) {
      result = new Mode(this, env, getArgs(), Mode.MAYBE_ONE_SOLUTION);
      if (result.numOutputs() == getArgs().size() - 1)
        result.setSolutions(Mode.ONE_SOLUTION);
    }
    return result;
  }

  /** Set the mode that will be used to evaluate this predicate.
   @param mode Must be one of the modes returned previously by chooseMode.
   */
  //@ ensures evalMode_ == mode;
  public void setMode( /*@non_null@*/Mode mode)
  {
    assert this == mode.getParent();
    evalMode_ = mode;
    solutionsReturned_ = -1;
  }

  //@ requires getMode() != null;
  public void startEvaluation()
  {
    solutionsReturned_ = 0;
  }

  /** Generates the next solution that satisfies this predicate.
   This must only be called after startEvaluation().
   @return true iff another solution has been found.
   */
  //@ requires getMode() != null;
  //@ requires solutionsReturned >= 0;
  public abstract boolean nextEvaluation();

  /** Convenience method to convert a ZName into a string.
   *  (This controls whether we print internal names with Ids or not.)
   * @return
   */
  public static String printName(ZName name)
  {
    // add the getId part if you want to show Ids of names within FlatPreds.
    return printer_.visitZName(name); // + name.getId();
  }

  /** Pretty-prints the name of the i'th argument, via nameString.
   *  If argNum < 0, then this just prints '_', which indicates
   *  an optional argument that is not present.
   */
  protected String printArg(int argNum)
  {
    if (argNum < 0)
      return "_";
    return printName(args_.get(argNum));
  }

  /** Pretty-prints getLastArg() */
  protected String printLastArg()
  {
    return printName(getLastArg());
  }

  /** A default implementation of toString.
   This returns "FlatXXX(args[0], args[1], ...)".
   */
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    String fullName = this.getClass().getName();
    int dotPos = fullName.lastIndexOf('.') + 1; // -1 becomes 0.
    result.append(fullName.substring(dotPos));
    result.append("[");
    for (ZName arg : getArgs()) {
      result.append(printName(arg));
      result.append(",");
    }
    result.setCharAt(result.length()-1, ']');
    return result.toString();
  }

  /** A toString method for binary operators.
   *  For example, binOpString("+") gives "x + y = z",
   *  assuming that args_ contains [x,y,z].
   */
  protected String printBinOp(String op)
  {
    assert args_.size() == 3;
    return printArg(2) + " = " + printArg(0) + " " + op + " " + printArg(1);
  }

  protected String printQuant(String quant, String stext, String body,
      String endQuant)
  {
    if (stext.contains("\n") || body.contains("\n")) {
      return quant + "\n" + INDENT + indent(stext) + "\n@ " + indent(body)
            + "\n" + endQuant;
    }
    else {
      return quant + " " + stext + " @ " + body + endQuant;
    }
  }

  /** Indents a multi-line string by replacing all newlines
   *  by a newline followed by two spaces.
   * @param str the (possibly multi-line) string to indent
   * @return  same as str, but perhaps with additional spaces
   */
  public String indent(String str)
  {
    return str.replaceAll("\n", "\n" + INDENT);
  }

  ///////////////////////// Pred methods ///////////////////////

  /** Calls visitor.visitPred (preferably) or visitor.visitTerm.
   Subclasses that correspond to particular kinds of Pred
   should override this to call more specific visitXXX methods
   (and should call super to handle the remaining cases).
   */
  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatPredVisitor)
      return ((FlatPredVisitor<R>) visitor).visitFlatPred(this);
    else
      return null;
  }
}
