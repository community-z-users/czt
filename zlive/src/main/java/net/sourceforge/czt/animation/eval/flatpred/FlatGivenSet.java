/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.flatpred;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Set;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatGivenSetVisitor;
import net.sourceforge.czt.animation.eval.result.GivenValue;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** An extensible set of 'unknown' values (represented by strings).
 * @author Mark Utting
 */
public class FlatGivenSet extends FlatPred
{
  /** We need to call zlive_.getGivenSetSize(). */
  private ZLive zlive_;

  /** The name of this given set. */
  private String name_;

  /** The members of this given set. */
  Set<GivenValue> members_ = new TreeSet<GivenValue>(ExprComparator.create());

  /** The members left for nextMember() to return */
  private LinkedList<GivenValue> exampleMembers_;

  /** Number of members returned by nextMember() */
  private int membersReturned_;

  public FlatGivenSet(ZName set, String name, ZLive zlive)
  {
    args_ = new ArrayList<ZName>();
    args_.add(set);
    name_ = name;
    zlive_ = zlive;
    solutionsReturned_ = -1;
    exampleMembers_ = null;
  }

  public double getApproxSize()
  {
    return zlive_.getGivenSetSize();
  }

  /** The name of this given set. */
  public String getName()
  {
    return name_;
  }

  public boolean contains(Object obj)
  {
    if (obj instanceof GivenValue) {
      members_.add( (GivenValue)obj );
      return true;
    }
    else
      return false;
  }

  /** The lower bound on numeric elements, if any, else null. */
  public BigInteger getLower()
  {
    return null;
  }

  /** The upper bound on numeric elements, if any, else null. */
  public BigInteger getUpper()
  {
    return null;
  }

  /** The maximum size of the set in the default environment.
   *  @return  Upper bound on the size of the set, or null if not known.
   */
  public BigInteger maxSize()
  {
    return new BigInteger( String.valueOf( zlive_.getGivenSetSize() ));
  }

  /** Estimate the size of the set in the default environment.
   *  The default environment should have been set
   *  (via FlatPred.setMode) before you can call this.
   */
  public double estSize()
  {
    return estSize(getEnvir());
  }

  /** Estimate the size of the set in a given environment. */
  public double estSize(Envir env)
  {
    return zlive_.getGivenSetSize();
  }

  /** Always throws an exception, since the size of given sets is unknown. */
  public int size()
  {
    throw new EvalException("GIVEN "+name_+" has unknown size.");
  }

  public double estSubsetSize(Envir env, ZName elem)
  {
    return zlive_.getGivenSetSize();
  }

  /** To given sets are equal iff they are the same set.
   *  That is, they have the same name.
   */
  public boolean equals(Object obj)
  {
    if (obj instanceof FlatGivenSet)
      return name_.equals(((FlatGivenSet)obj).name_);
    else
      return false;
  }

  @Override
  public Mode chooseMode(Envir env)
  {
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue(args_.get(0), null);   // TODO
    return m;
  }

  @Override
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    boolean result = false;
    ZName set = args_.get(args_.size()-1);
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      if (evalMode_.isInput(getLastArg())) {
        Expr otherSet = evalMode_.getEnvir().lookup(set);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(set, null);   // TODO
        result = true;
      }
    }
    // take a copy of members_ to iterate through.
    // (we don't iterate through members_ itself,
    //  because it may change during the iteration).
    exampleMembers_ = new LinkedList<GivenValue>(members_);
    membersReturned_ = 0;
    return result;
  }

  protected Expr nextMember()
  {
    assert solutionsReturned_ > 0;
    if (exampleMembers_.size() > 0) {
      membersReturned_++;
      return exampleMembers_.remove();
    }
    else if (membersReturned_ < 1000) {   // TODO: do we need this hard limit?
      // generate some members
      membersReturned_++;
      if (membersReturned_ <= zlive_.getGivenSetSize())
        return new GivenValue(name_ + membersReturned_);
      else
        return null;
    }
    else
      throw new EvalException("GIVEN " + name_ + " is too big to iterate through.");
  }

  @Override
  public String toString()
  {
    return "GIVEN " + name_;
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatGivenSetVisitor)
      return ((FlatGivenSetVisitor<R>) visitor).visitFlatGivenSet(this);
    else
      return super.accept(visitor);
  }
}
