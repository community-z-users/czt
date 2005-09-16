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

import java.util.*;
import java.math.*;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/**
* @author Mark Utting
*
* This defines the interface to all different kinds of set objects.
* FlatMember(s,e) implements e \in s, where s can be any kind of
* set that implements the EvalSet interface.
*/
public class FlatMember extends FlatPred {
  
  /** This is non_null during evaluation */
  protected EvalSet set_;
  
  /** This is for iterating through set_ */
  protected Iterator current_;

  /** Membership of a set.
   * 
   * @param set      Must evaluate to an EvalSet object.
   * @param element  The member of the set.
   */
  public FlatMember(ZRefName set, ZRefName element)
  {
    args = new ArrayList(2);
    args.add(set);
    args.add(element);
    solutionsReturned = -1;
  }

  /** Membership of a set.
   * 
   * @param newargs  [set,member]
   */
  //@ requires newargs != null && newargs.size() == 2;
  public FlatMember(ArrayList newargs)
  {
    if (newargs == null || newargs.size() != 2)
      throw new IllegalArgumentException("FlatMember requires 2 args");
    args = newargs;
    solutionsReturned = -1;
  }
  
  public Mode chooseMode(Envir env)
  {
    // the set must be defined in env.
    ZRefName setName = args.get(0);
    ZRefName elemName = args.get(1);
    Mode m = null;
    if (env.isDefined(setName)) {
      ArrayList inputs = new ArrayList(2);
      inputs.add(Boolean.TRUE);
      if (env.isDefined(elemName)) {
        inputs.add(Boolean.TRUE);  // element is also an input
        m = new Mode(env, inputs, 0.5);
      } else {
        inputs.add(Boolean.FALSE); // element is an output
        // the actual EvalSet object will be available at evaluation
        // time, but we check to see if it is already available.
        // If it is, we can get better estimates.
        double solns = 0.0;
        Expr e = env.lookup(setName);
        if (e != null && e instanceof EvalSet)
          solns = ((EvalSet)e).estSize(env);
        else
          solns = Double.POSITIVE_INFINITY;
        Envir newEnv = env.add(elemName, null);
        m = new Mode(newEnv, inputs, solns);
      }
    }
    return m;
  }
 
  public void startEvaluation()
  {
    super.startEvaluation();
    assert solutionsReturned == 0;
    set_ = (EvalSet)evalMode_.getEnvir().lookup(args.get(0));
    assert(set_ != null);
  }
  
  public boolean nextEvaluation() {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    assert set_ != null;
    boolean result = false;
    ZRefName element = args.get(1);
    if (evalMode_.isInput(1)) {
      // do a membership test
      current_ = null;
      if (solutionsReturned == 0) {
        // we only do the membership test once
        solutionsReturned++;
        Expr arg1 = evalMode_.getEnvir().lookup(element);
        if (set_.isMember(arg1))
          result = true;
      }
    }
    else {
      // iterate through the members of set_
      if (solutionsReturned == 0) {
        // set up the iterator...
        current_ = set_.members();
      }
      assert current_ != null;
      solutionsReturned++;
      if (current_.hasNext()) {
        Expr value = (Expr)current_.next();
        evalMode_.getEnvir().setValue(element, value);
        result = true;
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatMemberVisitor) {
      FlatMemberVisitor flatMemberVisitor = (FlatMemberVisitor) visitor;
      return flatMemberVisitor.visitFlatMember(this);
    }
    return super.accept(visitor);
  }
}
