/**
Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.animation.eval.flatpred;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.UndefException;
import nz.ac.waikato.modeljunit.Action;
import nz.ac.waikato.modeljunit.FsmModel;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * An FSM model of the behaviour of FlatPred objects.
 * This is designed to be used with the ModelJUnit model-based
 * testing library.
 *
 * @author Mark Utting
 */
public class FlatPredModel implements FsmModel
{
  /** The FlatPred object that is being tested. */
  private FlatPred pred_;

  /** The names of all the free variables of the FlatPred. */
  private ZName[] names_;

  /** A comma-separated list of the valid mode triples.
   *  Eg. "OOO,IIO,III".  This controls whether the various
   *  chooseModeXXX actions expect chooseMode to succeed or not.
   */
  private String validModes_;

  /** Example values for startEval1 */
  private /*@non_null@*/ Eval eval1_;

  /** Example values for startEval2 */
  private Eval eval2_;

  /** The possible main states of the FlatPred. */
  enum State {Init, NoMode, GotMode, Started, Finished};
  private State state_;

  /** Bounds for the predicate under test. */
  private Bounds bounds_ = new Bounds(null);

  /** The input environment being used for testing. */
  //@invariant env_ == null <==> mode_ == null;
  private Envir env_;

  /** The mode that has currently been set. */
  //@invariant mode_ == null <==> (state_==Init || state_==NoMode);
  private Mode mode_;

  /** The data being used for the current evaluation. */
  //@invariant data_ != null <==> state_==Started;
  private Eval data_;


  /** Create a test harness for a FlatPred subclass.
   *  For example, if toTest represents the constraint a*b=c,
   *  then names should contain {a,b,c} and eval1 and eval2 might contain
   *  some valid values like {2,3,6} or invalid values like {2,5,11}.
   *
   * @param toTest  An instance of a FlatPred subclass.
   * @param names   The free variables of the toTest object.
   * @param validModes A comma-separated string containing all the modes
   *                that are valid for this predicate.  These must be a
   *                subset of OOO, OII, IOI, IIO, III.  If you have only 2
   *                names, then IOI=III.  If you have only 1 name, then
   *                OOO=OII and IOI=IIO=III.
   * @param eval1   Example values for names.
   * @param eval2   Example values for names.
   */
  //@requires names.length == eval1.args.length;
  //@requires names.length == eval2.args.length;
  public FlatPredModel(FlatPred toTest, ZName[] names, String validModes,
      Eval eval1, Eval eval2)
  {
    StringBuffer namestr = new StringBuffer();
    namestr.append("[");
    for (ZName n : names)
      namestr.append(n.toString() + ",");
    namestr.append("]");
    debug("============= STARTING TO TEST " + toTest + namestr);
    pred_ = toTest;
    names_ = names;
    validModes_ = validModes;
    eval1_ = eval1;
    eval2_ = eval2;
    reset(true);
  }

  /** Debugging messages that can be printed to System.out/err. */
  public void debug(String msg)
  {
    // System.out.println("DEBUG: "+msg);
  }

  public String getState()
  {
    StringBuffer result = new StringBuffer();
    result.append(state_.toString());
    if (env_ != null) {
      // add the mode to the end of the state.
      for (int i=0; i<names_.length; i++) {
        if ( ! env_.isDefined(names_[i]))
          result.append('O');
        else
          result.append('I');  // an input
      }
    }
    return result.toString();
  }

  /** Resets the implementation under test.
   *  TODO: it would be nice to be able to actually reset the FlatPred.
   *  Then we could reset/recreate bounds_ as well.
   * @param testing true if this is a real test run (currently ignored).
   */
  public void reset(boolean testing)
  {
    state_ = State.Init;
    env_ = null;
    mode_ = null;
    data_ = null;
    debug("reset");
  }

  public boolean inferBoundsGuard() {return state_ == State.Init; }
  /** Infers as precise a fixed point as possible. */
  @Action public void inferBounds()
  {
    int deductions = 1;
    while (deductions > 0) {
      bounds_.startAnalysis();
      pred_.inferBounds(bounds_);
      bounds_.endAnalysis();
      deductions = bounds_.getDeductions();
      debug("inferBounds did "+deductions+" deductions, bounds="+bounds_);
    }
    state_ = State.NoMode;
  }

  /** A helper method for the chooseModeXXX actions.
   *  @param inout  String of three 'I' (input) or 'O' (output) chars.
   *   The three chars control whether names_[0]/names_[2..N-2]/names_[N-1]
   *   are inputs or outputs, respectively.
   */
  //@requires inout.length == 3;
  public void chooseMode(String inout)
  {
    assert inout.length() == 3;
    boolean isInput[] = new boolean[names_.length];
    env_ = new Envir();
    // Is names_[0] an input?
    isInput[0] = inout.charAt(0) == 'I';
    // Are names_[1..length-2] inputs?
    for (int i=1; i <= names_.length - 2; i++)
      isInput[i] = inout.charAt(1) == 'I';
    // Is names_[length-1] an input?
    isInput[names_.length - 1] = inout.charAt(2) == 'I';

    // Now add the inputs into env.
    for (int i=0; i < names_.length; i++)
      if (isInput[i])
        env_ = env_.plus(names_[i], null);
    boolean shouldWork = validModes_.contains(inout);

    mode_ = pred_.chooseMode(env_);
    debug("chooseMode("+env_+") --> "+mode_);
    if (shouldWork)
      Assert.assertNotNull("Valid mode expected, but got null",mode_);
    else
      Assert.assertNull("Null mode expected, but got "+mode_, mode_);
    if (mode_ == null) {
      state_ = State.NoMode;
      env_ = null;
    }
    else {
      // now check that mode is correct.
      for (int i=0; i<names_.length; i++) {
        Assert.assertEquals("name["+i+"] = "+names_[i], 
            isInput[i], mode_.isInput(names_[i]));
      }
      pred_.setMode(mode_);
      // check that all names are defined in the output environment.
      Envir newenv = mode_.getEnvir();
      for (int i=0; i<names_.length; i++)
        Assert.assertTrue(names_[i]+" should be defined",
            newenv.isDefined(names_[i]));
      state_ = State.GotMode;
      // NOTE that env_ is left as the input environment.
    }
  }

  /** Tries chooseMode with no inputs. */
  public boolean chooseModeOOOGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeOOO()
  {
    chooseMode("OOO");
  }

  /** Tries chooseMode with all names except the last being inputs. */
  public boolean chooseModeIIOGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeIIO()
  {
    chooseMode("IIO");
  }

  /** Tries chooseMode with all names except the second one being inputs. */
  public boolean chooseModeIOIGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeIOI()
  {
    chooseMode("IOI");
  }

  /** Tries chooseMode with all names except the first one being inputs. */
  public boolean chooseModeOIIGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeOII()
  {
    chooseMode("OII");
  }

  /** Tries chooseMode with all names being inputs. */
  public boolean chooseModeIIIGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeIII()
  {
    chooseMode("III");
  }

  /** Checks that we are in State.GotMode and that the current mode
   *  is compatible with data.modes.
   */
  protected boolean startEvalGuard(Eval data)
  {
    boolean result = state_ == State.GotMode;
    for (int i=0; result && i<names_.length; i++) {
      if (env_.isDefined(names_[i])) {
        // names_[i] is an input, so 'I' or '?' is allowed.
        if (data.modes.charAt(i) == 'O')
          result = false;
      }
      else {
        // names_[i] is an output, so 'O' or '?' is allowed.
        if (data.modes.charAt(i) == 'I')
          result = false;
      }
    }
    return result;
  }

  /** Helper method for starting a new evaluation.
   *  @param data The data values and modes which can be used.
   */
  //@requires env_ != null;
  public void startEval(/*@non_null@*/ Eval data)
  {
    // Note: we use the original env here, as given to chooseMode.
    for (int i=0; i<names_.length; i++) {
      if (env_.isDefined(names_[i])) {
        Expr value = data.args[i];
        env_.setValue(names_[i], value);
      }
    }
    debug("startEval with env="+env_);
    pred_.startEvaluation();
    data_ = data;
    state_ = State.Started;
  }

  /** Starts a new evaluation using the eval1_ data. */
  public boolean startEval1Guard() { return startEvalGuard(eval1_); }
  @Action public void startEval1()
  {
    startEval(eval1_);
  }

  /** Starts a new evaluation using the eval2_ data. */
  public boolean startEval2Guard() { return startEvalGuard(eval2_); }
  @Action public void startEval2()
  {
    startEval(eval2_);
  }

  public boolean nextEvalGuard() {return state_ == State.Started; }
  /** Call nextEvaluation() the expected number of times,
   *  and check that it returns true (or throws an exception).
   */
  @Action public void nextEval()
  {
    assert data_ != null;
    debug("nextEval trying nextEval() "+data_.successes+" times.");
    if (data_.successes > 1) {
      // just check that true is returned the expected number of times.
      for (int i = data_.successes; i > 0; i--)
        Assert.assertTrue(pred_.nextEvaluation());
    }
    else if (data_.successes == 1) {
      Assert.assertTrue("nextEvaluation should be true",
          pred_.nextEvaluation());
      // check that the correct results were returned.
      Envir newenv = pred_.getEnvir();
      debug("nextEval returns newenv="+newenv);
      for (int i=0; i<names_.length; i++) {
        Assert.assertTrue(names_[i]+" undefined.",
            newenv.isDefined(names_[i]));
        Assert.assertEquals(names_[i]+" has incorrect value.",
            data_.args[i], newenv.lookup(names_[i]));
      }
    }
    else if (data_.successes == Eval.UNDEF) {
      try {
        pred_.nextEvaluation();
        Assert.fail("Should have thrown UndefException: "+pred_);
      }
      catch (UndefException ex) {
        // Good!
      }
    }
    // else data_.successes == 0, so we do nothing.
    data_ = null;
    state_ = State.Finished;
  }

  public boolean nextEvalFalseGuard() {return state_ == State.Finished; }
  /** Checks that nextEvaluation() returns false. */
  public @Action void nextEvalFalse()
  {
    boolean result = pred_.nextEvaluation();
    debug("nextEvalFalse gives "+result+" with env="+env_);
    Assert.assertFalse(result);
  }

  public boolean newEvalGuard() {return state_ == State.Started
                                     || state_ == State.Finished;  }
  /** Go back and start a new evaluation, using the same mode. */
  @Action public void newEval()
  {
    debug("newEval with env="+env_);
    data_ = null;
    state_ = State.GotMode;
  }

  public boolean newModeGuard() {return state_ == State.Started
                                     || state_ == State.Finished
                                     || state_ == State.GotMode; }
  /** Go back and try a new mode. */
  @Action public void newMode()
  {
    debug("newMode with env="+env_);
    mode_ = null;
    env_  = null;
    data_ = null;
    state_ = State.NoMode;
  }
}




