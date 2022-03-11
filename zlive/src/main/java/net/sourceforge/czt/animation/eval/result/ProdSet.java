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

package net.sourceforge.czt.animation.eval.result;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.UndefException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.Factory;

/**
 * A simple implementation of a cartesian product set.
 *
 * @author Petra Malik
 */
public class ProdSet extends DefaultEvalSet
{
  private List<EvalSet> baseSets_;
  private ProdSetIterator iter_;

  public ProdSet(List<EvalSet> baseSets)
  {
    baseSets_ = baseSets;
    iter_ = new ProdSetIterator();
  }

  /** Returns the exact size of the set,
   *  or MAX_VALUE if the set is infinite or
   *  has cardinality greater than MAX_VALUE.
   */
  @Override
  public int size()
  {
    if (baseSets_.size() == 0) {
      throw new UndefException("cartesian product over no sets");
    }
    // multiply the exact sizes of the bases sets together.
    // if some are infinite (represented by Integer.MAX_VALUE) the result will be really big,
    // so we must return Integer.MAX_VALUE (to represent infinity).
    BigInteger result = BigInteger.ONE;
    for (EvalSet s : baseSets_) {
      result = result.multiply(BigInteger.valueOf(s.size()));
    }
    if (result.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
      return Integer.MAX_VALUE;
    }
    return result.intValue();
  }

  /** Returns the exact size of the set, or
   *  null if it is likely to be infinite.
   */
  @Override
  public BigInteger maxSize()
  {
    if (baseSets_.size() == 0) {
      throw new UndefException("cartesian product over no sets");
    }
    BigInteger result = BigInteger.ONE;
    boolean hasInfiniteSet = false;
    for (EvalSet s : baseSets_) {
      BigInteger smax = s.maxSize();
      if (smax == null) {
    	hasInfiniteSet = true;
      } else {
        result = result.multiply(s.maxSize());
      }
    }
    if (hasInfiniteSet && result.equals(BigInteger.ZERO)) {
    	hasInfiniteSet = false;  // empty sets win!
    }
    if (hasInfiniteSet) {
    	return null;
    }
    return result;
  }

  @Override
  public boolean contains(Object e)
  {
    if ( !(e instanceof TupleExpr)) {
      String msg = "Type error: members of ProdSet must be a tuple: " + e;
      throw new EvalException(msg);
    }
    ZExprList list = ((TupleExpr) e).getZExprList();
    if (list.size() != baseSets_.size()) return false;
    Iterator<Expr> tupleIter = list.iterator();
    Iterator<EvalSet> baseIter = baseSets_.iterator();
    while (tupleIter.hasNext()) {
      if (! baseIter.next().contains(tupleIter.next())) return false;
    }
    return true;
  }

  @Override
  protected Expr nextMember()
  {
    if (iter_.hasNext()) {
      return iter_.next();
    }
    return null;
  }

  @Override
  protected void resetResult()
  {
    super.resetResult();
  }

  public List<EvalSet> getBaseSets()
  {
    return baseSets_;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof ProdSetVisitor) {
      return ((ProdSetVisitor<R>)visitor).visitProdSet(this);
    }
    return super.accept(visitor);
  }

  public String toString()
  {
    return "Prod(" + baseSets_ + ")";
  }

  protected class ProdSetIterator
  {
    private Factory factory_ = new Factory();
    private List<Iterator<Expr>> iterList_ = new ArrayList<Iterator<Expr>>();
    private List<Expr> currExprs_;

    public ProdSetIterator()
    {
      for (EvalSet s : baseSets_) {
        Iterator<Expr> iter = s.iterator();
        iterList_.add(iter);
      }
    }

    public boolean hasNext()
    {
      if (currExprs_ == null) {
        for (Iterator<Expr> iter : iterList_) {
          if (! iter.hasNext()) {
            return false;
          }
        }
        return true;
      }
      for (Iterator<Expr> iter : iterList_) {
        if (iter.hasNext()) {
          return true;
        }
      }
      return false;
    }

    public TupleExpr next()
    {
      if (! hasNext()) throw new NoSuchElementException();
      if (currExprs_ == null) {
        currExprs_ = new ArrayList<Expr>();
        for (Iterator<Expr> iter : iterList_) {
          currExprs_.add(iter.next());
        }
      }
      else {
        ListIterator<Iterator<Expr>> iterIter = iterList_.listIterator();
        ListIterator<Expr> exprIter = currExprs_.listIterator();
        Iterator<EvalSet> baseIter = baseSets_.iterator();
        boolean updated = false;
        while (! updated && iterIter.hasNext()) {
          assert exprIter.hasNext();
          assert baseIter.hasNext();
          Iterator<Expr> iter = iterIter.next();
          exprIter.next();
          EvalSet set = baseIter.next();
          if (iter.hasNext()) {
            exprIter.set(iter.next());
            updated = true;
          }
          else {
            iterIter.set(set.iterator());
          }
        }
        if (! updated) throw new NoSuchElementException();
      }
      ZExprList zExprList = factory_.createZExprList();
      for (Expr expr : currExprs_) {
        zExprList.add(expr);
      }
      return factory_.createTupleExpr(zExprList);
    }
  }
}
