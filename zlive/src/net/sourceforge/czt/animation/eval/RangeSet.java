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
import net.sourceforge.czt.base.impl.ListTermImpl;
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
public class RangeSet implements EvalSet {

  public final double DEFAULT_SIZE = 1000000.0;
  protected RefName lBound_;
  protected RefName uBound_;
  protected BigInteger lower_;
  protected BigInteger upper_;
  protected Envir envir_;
  protected List vars_;

  public RangeSet(RefName lowerBound, RefName upperBound)
  {
    lBound_ = lowerBound;
    uBound_ = upperBound;
    envir_ = null;
    vars_ = new ArrayList();
	vars_.add(lBound_);
    vars_.add(uBound_);
  }

  private BigInteger getBound(RefName bound)
  {
    Expr E = envir_.lookup(bound);
    if (E == null)
      return null;
    else {
      if (!(E instanceof NumExpr))
        throw new EvalException("Type Error for bound " + bound.getWord() + " = " + E);
      return ((NumExpr)E).getValue();
    }
  }

 /* public BigInteger getLower()
  {
	lower_ = getBound(lBound_);
	return lower_;
  }

  public BigInteger getUpper()
  {
	upper_ = getBound(uBound_);
	return upper_;
  }
*/
  public void setEnvir(Envir env)
  { envir_ = env; }

  public Envir getEnvir()
  { return envir_; }

  /** Estimate the size of the set. */
  public double estSize()
  {
    lower_ = getBound(lBound_);
    upper_ = getBound(uBound_);
    if (lower_ == null || upper_ == null)
      return DEFAULT_SIZE;
    if(upper_.compareTo(lower_)<0)
      return 0.0;
    else
      return (upper_.subtract(lower_).add(BigInteger.ONE).doubleValue());
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
    protected BigInteger current_;
    public setIterator()
    {
      current_ = lower_;
    }
    public boolean hasNext()
    {
      return (current_.compareTo(upper_) <= 0);
 	}
    public Object next()
    {
      BigInteger temp = current_;
      current_ = current_.add(BigInteger.ONE);
      return temp;
    }
    public void remove()
	{
	  throw new UnsupportedOperationException("The Remove Operation is not supported");
	}
  }


  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *
  * @return an Iterator object.
  */
  public Iterator members()
  {
    lower_ = getBound(lBound_);
    upper_ = getBound(uBound_);
    return (new setIterator());
  }

  /** Tests for membership of the set.
  * @param e  The fully evaluated expression.
  * @return   true iff e is a member of the set.
  */
  public boolean isMember(Expr e)
  {
    if ( !(e instanceof NumExpr))
      throw new EvalException("Type error: members of RangeSet must be numbers: " + e);
    BigInteger i = ((NumExpr)e).getValue();
    lower_ = getBound(lBound_);
    upper_ = getBound(uBound_);
    return ((lower_.compareTo(i) <= 0) && (upper_.compareTo(i) >= 0));
  }

  ///////////////////////// Pred methods ///////////////////////

  /** Returns an empty list.
  Subclasses could override this to return annotations if they wanted.
  */
  public ListTerm getAnns()
  { return new ListTermImpl(); }

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
