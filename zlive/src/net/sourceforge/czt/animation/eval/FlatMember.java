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

package net.sourceforge.czt.animation.eval;

import java.util.*;
import java.math.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/**
* @author Mark Utting
*
* This defines the interface to all different kinds of set objects.
*/
public class FlatMember {

  protected RefName left_;
  protected RefName set_;
  protected Mode evalMode_;
  protected boolean evalFlag_;
  protected Iterator current_;

  public FlatMember(RefName left, RefName set)
  {
    left_ = left;
    set_ = set;
    evalMode_ = null;
    evalFlag_ = false;
    current_ = null;
  }

  public Mode chooseMode(Envir env)
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    Expr zilch = factory_.createNumExpr(BigInteger.ZERO);
    Mode m = null;
    boolean[] inputs = new boolean[2];
    double solutions;
    if(env.isDefined(set_)) {
      if(env.lookup(set_) instanceof EvalSet) {
        List vars = ((EvalSet)env.lookup(set_)).freeVars();
        if( (env.lookup((RefName)(vars.get(0))) != null) && (env.lookup((RefName)(vars.get(1))) != null) ) {
          if(env.isDefined(left_)) {
            solutions = 0.5;
            inputs[0] = true;
            inputs[1] = true;
            m = new Mode(env,inputs,solutions);
          }
          else {
            ((EvalSet)env.lookup(set_)).setEnvir(env);
            solutions = ((EvalSet)env.lookup(set_)).estSize();
            inputs[0] = false;
            inputs[1] = true;
            env = env.add(left_,null);
            m = new Mode(env,inputs,solutions);
          }
        }
      }
    }
    return m;
  }

  public Mode getMode()
  { return evalMode_; }

  public void setMode(Mode m)
  {
    evalMode_ = m;
    //Looking up the set in the new evironment,
    //and then setting the environment variable in that set to m.getEnvir()
    ((EvalSet)m.getEnvir().lookup(set_)).setEnvir(m.getEnvir());
  }

  public void startEvaluation()
  { evalFlag_ = true;
 	current_ = null;
  }

  public boolean nextEvaluation()
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    boolean result = false;
    if(evalFlag_)
    {
      if (evalMode_!=null) {
        if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
          evalFlag_ = false;
          Expr a = evalMode_.getEnvir().lookup(left_);
          Expr b = evalMode_.getEnvir().lookup(set_);
          EvalSet y = (EvalSet)b;
          if (y.isMember(a))
            result = true;
          }
        else if (evalMode_.isInput(1)) {
          Expr b = evalMode_.getEnvir().lookup(set_);
          EvalSet y = (EvalSet)b;
          if(current_ == null) {
            current_ = y.members();
            Expr a = factory_.createNumExpr((BigInteger)(current_.next()));
            evalMode_.getEnvir().setValue(left_,a);
            result = true;
          }
          else {
            if(current_.hasNext()) {
              Expr a = factory_.createNumExpr(((BigInteger)current_.next()));
              evalMode_.getEnvir().setValue(left_,a);
              result = true;
            }
            else
              evalFlag_ = false;
          }
        }
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  /** Returns an empty list.
  Subclasses could override this to return annotations if they wanted.
  */
  public List getAnns()
  { return new ArrayList(); }

  /** Calls visitor.visitPred (preferably) or visitor.visitTerm.
  Subclasses that correspond to particular kinds of Pred
  should override this to call more specific visitXXX methods
  (and should call super to handle the remaining cases).
  */

  /** @czt.todo Implement this properly. */
  public Object accept(Visitor visitor)
  { //TODO: call memPredVisitor
    return this;
  }

  /** @czt.todo Implement this properly. */
  public /*@non_null@*/ Object[] getChildren()
  { return new Object[0]; }

  /** @czt.todo Implement this properly. */
  public Term /*@non_null@*/ create(Object[] args)
  { throw new RuntimeException("create not implemented"); }
}
