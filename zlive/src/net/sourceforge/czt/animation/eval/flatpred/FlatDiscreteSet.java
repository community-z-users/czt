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
import net.sourceforge.czt.base.impl.TermAImpl;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;

/**
* @author Mark Utting
*
* FlatDiscreteSet(A,s) implements {Elements of ArrayList A} = s
*/
public class FlatDiscreteSet
  extends FlatPred
  implements EvalSet
{
  protected Factory factory_ = new Factory();
  protected Set vars_ = new HashSet();
  
  /** Contains the enumerated members of the set. */
  protected Set iterateSet_;

  public FlatDiscreteSet(List elements, RefName set)
  {
	Object itNext;
    args = new ArrayList();
    // Create a map to remove duplicate RefNames
    Map map = new HashMap();
    for(int i=0;i<elements.size();i++)
      map.put(elements.get(i),elements.get(i));
    Iterator it = map.values().iterator();
    while(it.hasNext()) {
      itNext = it.next();
      vars_.add(itNext);
      args.add(itNext);
    }
    args.add(set);
    solutionsReturned = -1;
    iterateSet_ = null;
  }

  //@ requires newargs.size() >= 1;
  public FlatDiscreteSet(List newargs)
  {
	this(newargs.subList(0,newargs.size()-2),
			(RefName)newargs.get(newargs.size()-1));
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return modeFunction(env);
  }

  /** Estimate the size of the set. */
  public double estSize()
  {
    assert(evalMode_ != null);
    assert(vars_ != null);
    return ((double)vars_.size());
  }

  /** A list of all the free variables that this set depends upon.
  * @return The free variables.
  */
  public Set freeVars()
  {
    return vars_;
  }

  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *
  * @return an Iterator object.
  */
  public Iterator members() {
    if (iterateSet_ == null) {
      //System.out.println("DEBUG: inside discreteSet env="+evalMode_.getEnvir().toString());
      //System.out.println("DEBUG: in FlatDiscreteSet q="+((NumExpr)evalMode_.getEnvir().lookup((RefName)args.get(5))).getValue());

      iterateSet_ = new HashSet();
      Envir env = evalMode_.getEnvir();
      for (Iterator i = vars_.iterator(); i.hasNext();) {
        Expr value = (Expr)env.lookup((RefName)i.next());
        //System.out.println("DEBUG: value="+((NumExpr)value).getValue());
        iterateSet_.add(value);
      }

    }
    //System.out.println("DEBUG: final discrete set size="+iterateSet_.size());
    return iterateSet_.iterator();
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    for (int i=0;i<args.size()-1;i++)
      assert evalMode_.isInput(i);
    boolean result = false;
    RefName set = (RefName)args.get(args.size()-1);
    iterateSet_ = null;
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(args.size()-1)) {
        Expr otherSet = evalMode_.getEnvir().lookup(set);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(set, this);
        result = true;
      }
    }
    return result;
  }

  /** Tests for membership of the set.
  * @param e  The fully evaluated expression.
  * @return   true iff e is a member of the set.
  */
  public boolean isMember(/*@non_null@*/Expr e)
  {
    assert (e != null);
    assert (evalMode_ != null);
    boolean result = false;
    Iterator i = vars_.iterator();
    while( ! result && i.hasNext()) {
      Expr value = evalMode_.getEnvir().lookup((RefName)i.next());
      if(e.equals(value))
        result = true;
    }
    return result;
  }

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatDiscreteSetVisitor) {
      FlatDiscreteSetVisitor flatDiscreteSetVisitor = (FlatDiscreteSetVisitor) visitor;
      return flatDiscreteSetVisitor.visitFlatDiscreteSet(this);
    }
    return super.accept(visitor);
  }

  /** True iff two EvalSets contain the same elements. */
  public boolean equals(Object otherSet) {
    if (otherSet instanceof EvalSet)
      return equalsEvalSet(this,(EvalSet)otherSet);
    else
      return false;
  }
}
