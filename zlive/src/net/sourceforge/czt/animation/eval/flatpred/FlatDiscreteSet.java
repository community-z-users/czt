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
  protected ArrayList vars_ = new ArrayList();

  public FlatDiscreteSet(ArrayList elements, RefName set)
  {
    // Create a map to remove duplicate RefNames
    Map map = new HashMap();
    for(int i=0;i<elements.size();i++)
      map.put(elements.get(i),elements.get(i));
    Iterator it = map.values().iterator();
    while(it.hasNext())
      vars_.add(it.next());
    args = elements;
    args.add(set);
    solutionsReturned = -1;
  }

  //@ requires newargs.size() >= 1;
  public FlatDiscreteSet(ArrayList newargs)
  {
    if (newargs == null || newargs.size() < 1)
      throw new IllegalArgumentException("FlatDiscreteSet requires at least 1 arg");
    // Create a map to remove duplicate RefNames
    Map map = new HashMap();
    for(int i=0;i<args.size()-1;i++)
      map.put(args.get(i),args.get(i));
    Iterator it = map.values().iterator();
    while(it.hasNext())
      vars_.add(it.next());
    args = newargs;
    solutionsReturned = -1;
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
  public List freeVars()
  {
    return vars_;
  }

  private class setIterator implements Iterator
  {
    protected int counter;
    public setIterator()
    { counter=0; }
    public boolean hasNext()
    { return (counter<vars_.size()); }
    public Object next()
    {
      return evalMode_.getEnvir().lookup((RefName)vars_.get(counter++));
    }
    public void remove()
    { throw new UnsupportedOperationException("The Remove Operation is not supported"); }
  }


  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *
  * @return an Iterator object.
  */
  public Iterator members()
  {
    return (new setIterator());
  }

  public boolean equals(Object other)
  {
    boolean result = false;
    if(other instanceof EvalSet) {
      Set thisSet = new HashSet();
      Set otherSet = new HashSet();
      Iterator it = ((EvalSet)other).members();
      while(it.hasNext()) {
        otherSet.add(it.next());
      }
      it = this.members();
      while(it.hasNext()) {
        thisSet.add(it.next());
      }
      if (thisSet.equals(otherSet))
        result = true;
    }
    return result;
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
    assert (e!=null);
    assert (evalMode_!=null);
    Expr expr = null;
    boolean result = false;
    int i = 0;
    while( (i<vars_.size()) && (!result)) {
      expr = evalMode_.getEnvir().lookup((RefName)vars_.get(i));
      if(e.equals(expr))
        result = true;
      i++;
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


  /** This implementation of equals handles FlatRangeSets efficiently.
  if (otherSet instanceof FlatRangeSet) {
    FlatRangeSet other = (FlatRangeSet)otherSet;
    result = lower_.equals(other.lower_) && upper_.equals(other.upper_);
  } else {
  */

}
