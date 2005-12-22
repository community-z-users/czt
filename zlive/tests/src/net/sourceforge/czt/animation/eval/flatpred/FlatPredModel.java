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
import net.sourceforge.czt.modeljunit.transition;
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
  
  /** Example values that should satisfy the FlatPred. */
  private Expr[]     goodValues_;

  /** The possible main states of the FlatPred. */
  enum State {Init, NoMode, GotMode, StartedEval, DoneEval};
  private State state_;

  /** The environment being used for testing. */
  private Envir env_;

  /** The mode that has currently been set. */
  private Mode mode_;
  
  /** The input values that have been chosen.
   *  Note that values_[i] will be either null, goodlValues_[i], or badValues_[i].
   */
  private Expr[] values_;

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
  public FlatPredModel(FlatPred toTest, ZRefName[] names, Expr[] goodValues)
  {
    pred_ = toTest;
    names_ = names;
    goodValues_ = goodValues;
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
        else if (values_ != null
            && values_[i] != null
            && values_[i].equals(goodValues_[i]))
          result.append('I');  // good input
        else
          result.append('i');  // bad input
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
    values_ = null;
    result_ = false;
  }

  public boolean skipInferBoundsGuard() {return state_ == State.Init; }
  public @transition void skipInferBounds()
  {
    state_ = State.NoMode;
  }

  /** Tries chooseMode with no inputs. */
  public boolean chooseModeOOOGuard() {return state_ == State.NoMode; }
  public @transition void chooseModeOOO()
  {
    env_ = new Envir();
    Assert.assertNull("should not return a mode", pred_.chooseMode(env_));
    state_ = State.NoMode;  // unchanged
  }

  /** Tries chooseMode with all names being inputs. */
  public boolean chooseModeIIIGuard() {return state_ == State.NoMode; }
  public @transition void chooseModeIII()
  {
    System.err.println("chooseModeIII");
    env_ = new Envir();
    for (int i=0; i<names_.length; i++) {
      env_ = env_.add(names_[i], goodValues_[i]);
      System.err.println("Added name "+names_[i]+" with value "+goodValues_[i]);
    }
    System.err.println("new env = "+env_);
    mode_ = pred_.chooseMode(env_);
    System.err.println("mode was "+mode_);
    Assert.assertNotNull(mode_);
    // now check that mode is correct.
    for (int i=0; i<names_.length; i++) {
      Assert.assertEquals(true, mode_.isInput(i));
    }
    pred_.setMode(mode_);
    state_ = State.GotMode;
  }

  /** Starts a new evaluation.
   *  TODO: have several of these, which choose between good/bad values.
   */
  public boolean startGoodEvalGuard() {return state_ == State.GotMode; }
  public @transition void startGoodEval()
  {
    values_ = new Expr[names_.length];
    for (int i=0; i<names_.length; i++) {
      if (env_.isDefined(names_[i])) {
        values_[i] = goodValues_[i];
        env_.setValue(names_[i], values_[i]);
      }
    }
    pred_.startEvaluation();
    result_ = pred_.nextEvaluation();
    if(result_) {
      // check that the result is correct
      for (int i=0; i<names_.length; i++) {
        Assert.assertEquals(env_.lookup(names_[i]), goodValues_[i]);
      }
    }
    state_ = State.DoneEval;
  }

  /** Continue calling nextEvaluation.
   *  This currently assumes a maximum of one solution.
   */
  public boolean continueEvalGuard() {return state_ == State.DoneEval && result_; }
  public @transition void continueEval()
  {
    result_ = pred_.nextEvaluation();
    Assert.assertFalse(result_);
    state_ = State.DoneEval; // unchanged
  }

  public boolean newEvalGuard() {return state_ == State.DoneEval; }
  public @transition void newEval()
  {
    state_ = State.GotMode;
  }
}




