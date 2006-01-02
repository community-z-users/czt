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
import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;


/**
 * An FSM model of the behaviour of FlatPred objects.
 * This is designed to be used with the ModelJUnit model-based
 * testing library.
 *
 * @author Mark Utting
 */
public class FlatPredModel
{
  /** The FlatPred object that is being tested. */
  private FlatPred pred_;
  
  /** The names of all the free variables of the FlatPred. */
  private ZRefName[] names_;
  
  /** Example values for startEval1 */
  private /*@non_null@*/ Eval eval1_;

  /** Example values for startEval2 */
  private Eval eval2_;

  /** The possible main states of the FlatPred. */
  enum State {Init, NoMode, GotMode, EvalTrue, EvalFalse};
  private State state_;

  /** The environment being used for testing. */
  private Envir env_;

  /** The mode that has currently been set. */
  private Mode mode_;

  /** The result of the previous operation (inferBounds or nextEvaluation). */
  private boolean result_;
  
  /** Create a test harness for a FlatPred subclass.
   *  The goodValues should be a correct evaluation for the toTest object.
   *  For example, if toTest represents the constraint a*b=c,
   *  then names should contain {a,b,c} and goodValues should contain
   *  some values like {2,3,6}.
   *  
   * @param toTest  An instance of a FlatPred subclass.
   * @param names   The free variables of the toTest object.
   * @param goodValues  Good values for each of the names.
   */
   //@requires names.length == values.length;
  public FlatPredModel(FlatPred toTest, ZRefName[] names,
        Eval eval1, Eval eval2)
  {
    pred_ = toTest;
    names_ = names;
    eval1_ = eval1;
    eval2_ = eval2;
    init(false);
  }

  public String toString()
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
   * @param testing true if this is a real test run (currently ignored).
   */
  public void init(boolean testing)
  {
    state_ = State.Init;
    env_ = null;
    mode_ = null;
    result_ = false;
  }

  public boolean skipInferBoundsGuard() {return state_ == State.Init; }
  @Action public void skipInferBounds()
  {
    state_ = State.NoMode;
  }

  /** A helper method for the chooseModeXXX actions */
  //@requires input.length == names_.length;
  public void chooseMode(boolean[] input, boolean shouldWork)
  {
    env_ = new Envir();
    for (int i=0; i<names_.length; i++) {
      if (input[i])
        env_ = env_.add(names_[i], eval1_.args[i]);
    }
    mode_ = pred_.chooseMode(env_);
    System.out.println("chooseMode("+env_+") --> "+mode_);
    // System.err.println("mode was "+mode_);
    Assert.assertEquals(mode_ != null, shouldWork);
    if (mode_ == null) {
      state_ = State.NoMode;
      env_ = new Envir();
    }
    else {
      // now check that mode is correct.
      for (int i=0; i<names_.length; i++) {
        Assert.assertEquals(input[i], mode_.isInput(i));
      }
      pred_.setMode(mode_);
      // check that all names are defined in the output environment.
      Envir newenv = mode_.getEnvir();
      for (int i=0; i<names_.length; i++)
        Assert.assertTrue(names_[i]+" is undefined", newenv.isDefined(names_[i]));
      state_ = State.GotMode;
      // NOTE that env_ is left as the input environment.
    }
  }

  /** Tries chooseMode with no inputs. */
  public boolean chooseModeOOOGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeOOO()
  {
    chooseMode(new boolean[] {false,false,false}, false);
  }

  /** Tries chooseMode with all names being inputs. */
  public boolean chooseModeIIIGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeIII()
  {
    chooseMode(new boolean[] {true,true,true}, true);
  }

  /** Tries chooseMode with all names except the last being inputs. */
  public boolean chooseModeIIOGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeIIO()
  {
    chooseMode(new boolean[] {true,true,false}, true);
  }
  
  /** Tries chooseMode with all names except the second one being inputs. */
  public boolean chooseModeIOIGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeIOI()
  {
    chooseMode(new boolean[] {true,false,true}, true);
  }
  
  /** Tries chooseMode with all names except the first one being inputs. */
  public boolean chooseModeOIIGuard() {return state_ == State.NoMode; }
  @Action public void chooseModeOII()
  {
    chooseMode(new boolean[] {false,true,true}, true);
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
  public void startEval(/*@non_null@*/ Eval data)
  {
    // Note: we use the original env here, as given to chooseMode.
    for (int i=0; i<names_.length; i++) {
      if (env_.isDefined(names_[i])) {
        Expr value = data.args[i];
        env_.setValue(names_[i], value);
      }
    }
    System.out.println("startEval with env="+env_);
    pred_.startEvaluation();
    result_ = false;
    // check that true is returned the expected number of times.
    for (int i = data.successes; i > 0; i--) {
      result_ = pred_.nextEvaluation();
      Assert.assertTrue(result_);
    }

    // check that the correct results were returned.
    if (data.successes == 1) {
      Envir newenv = pred_.getEnvir();
      System.out.println("nextEval returns newenv="+newenv);
      for (int i=0; i<names_.length; i++) {
        Assert.assertTrue(names_[i]+" undefined.",
            newenv.isDefined(names_[i]));
        Assert.assertEquals(names_[i]+" has incorrect value.",
            newenv.lookup(names_[i]), data.args[i]);
      }
    }
    state_ = result_ ? State.EvalTrue : State.EvalFalse;
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

  /** Continue calling nextEvaluation.
   *  This currently assumes a maximum of one solution.
   */
  public boolean continueEvalGuard() {return state_ == State.EvalTrue
                                          || state_ == State.EvalFalse; }
  @Action public void continueEval()
  {
    result_ = pred_.nextEvaluation();
    System.out.println("continueEval gives "+result_+" with env="+env_);
    Assert.assertFalse(result_);
    state_ = State.EvalFalse;
  }

  /** Go back and do a new evaluation, using the same mode. */
  public boolean newEvalGuard() {return state_ == State.EvalTrue
                                     || state_ == State.EvalFalse;  }
  @Action public void newEval()
  {
    System.out.println("newEval with env="+env_);
    state_ = State.GotMode;
  }
  
  /** Go back and try a new mode. */
  public boolean newModeGuard() {return state_ == State.EvalTrue
                                     || state_ == State.EvalFalse
                                     || state_ == State.GotMode; }
  @Action public void newMode()
  {
    System.out.println("newMode with env="+env_);
    state_ = State.NoMode;
  }
}




