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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;

/**
 * A power set with lazy evaluation of its elements.
 *
 * @author Petra Malik
 */
public class RelSet extends EvalSet
{
  private EvalSet from_;
  private EvalSet to_;
  private boolean function_;
  private boolean total_;
  private boolean onto_;
  private boolean injective_;

  /** Creates a new power set of the given base set. */
  public RelSet(EvalSet from,
                EvalSet to,
                boolean function,
                boolean total,
                boolean onto,
                boolean injective)
  {
    if (! function && injective) throw new UnsupportedOperationException();
    from_ = from;
    to_ = to;
    function_ = function;
    total_ = total;
    onto_ = onto;
    injective_ = injective;
  }

  public boolean isEmpty()
  {
    return false;
  }

  public int size()
  {
    return Integer.MAX_VALUE;
  }

  @Override
  public BigInteger maxSize()
  {
    return null;
  }

  @Override
  public double estSize()
  {
    return Double.POSITIVE_INFINITY;
  }

  /**
   * @throws EvalException if the given object is not an EvalSet.
   */
  public boolean contains(Object obj)
  {
    if ( !(obj instanceof EvalSet)) {
      String msg = "Type error: members of RelSet must be sets: " + obj;
      throw new EvalException(msg);
    }
    HashMap<Expr,Expr> map = new HashMap<Expr,Expr>();
    Set<Expr> range = new HashSet<Expr>();
    for (Expr expr : ((EvalSet) obj)) {
      if (!(expr instanceof TupleExpr)) return false;
      ZExprList exprList = ((TupleExpr) expr).getZExprList();
      if (exprList.size() != 2) return false;
      Expr left = exprList.get(0);
      Expr right = exprList.get(1);
      if (! from_.contains(left)) return false;
      if (! to_.contains(right)) return false;
      if (function_ || total_) {
        Expr to = map.get(left);
        if (to != null) {
          if (function_) return false;
        }
        else {
          map.put(left, right);
        }
      }
      if (onto_) range.add(right);
    }
    final int domSize = map.size();
    final int ranSize = range.size();
    if (total_ && domSize != from_.size()) return false;
    if (onto_ && ranSize != to_.size()) return false;
    if (injective_ && domSize != ranSize) return false;
    return true;
  }

  /**
   * @throws UnsupportedOperationException whenever this method is called.
   */
  @Override
  public Iterator<Expr> iterator()
  {
    throw new UnsupportedOperationException();
  }

  /**
   * @throws UnsupportedOperationException whenever this method is called.
   */
  @Override
  public ListIterator<Expr> listIterator()
  {
    throw new UnsupportedOperationException();
  }

  /**
   * @throws UnsupportedOperationException whenever this method is called.
   */
  @Override
  public Iterator<Expr> sortedIterator()
  {
    throw new UnsupportedOperationException();
  }

  /**
   * @throws UnsupportedOperationException whenever this method is called.
   */
  @Override
  public Iterator<Expr> subsetIterator(EvalSet otherSet)
  {
    throw new UnsupportedOperationException();
  }

  public String toString()
  {
    return "RelSet";
  }
}
