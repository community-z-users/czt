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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Set;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.ZString;

/**
 * A relation or function space, from_ &lt;--&gt; to_.
 * With various constraints (functional, total, onto or injective).
 *
 * @author Petra Malik
 */
public class RelSet extends EvalSet
{
  private Expr from_;  // will be an EvalSet at evaluation time
  private Expr to_;    // will be an EvalSet at evaluation time
  private boolean function_;
  private boolean total_;
  private boolean onto_;
  private boolean injective_;

  /** Creates a new power set of the given base set. */
  public RelSet(Expr from,
                Expr to,
                boolean function,
                boolean total,
                boolean onto,
                boolean injective)
  {
    if (! function && injective) {
      throw new UnsupportedOperationException("injective non-function relation");
    }
    from_ = from;
    to_ = to;
    function_ = function;
    total_ = total;
    onto_ = onto;
    injective_ = injective;
  }

  public Expr getDom()
  {
    return from_;
  }

  public Expr getRan()
  {
    return to_;
  }

  public boolean isFunction()
  {
    return function_;
  }

  public boolean isTotal()
  {
    return total_;
  }

  public boolean isOnto()
  {
    return onto_;
  }

  public boolean isInjective()
  {
    return injective_;
  }

  public boolean isEmpty()
  {
    return false;
  }

  /**
   *  TODO: calculate this correctly for functions with small/finite dom&ran.
   */
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
    return EvalSet.INFINITE_SIZE;  // most of them are infinite...
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
    EvalSet fromSet = (EvalSet) from_;
    EvalSet toSet = (EvalSet) to_;
    HashMap<Expr,Expr> map = new HashMap<Expr,Expr>();
    Set<Expr> range = new HashSet<Expr>();
    for (Expr expr : ((EvalSet) obj)) {
      if (!(expr instanceof TupleExpr))
        return false;
      ZExprList exprList = ((TupleExpr) expr).getZExprList();
      if (exprList.size() != 2)
        return false;
      Expr left = exprList.get(0);
      Expr right = exprList.get(1);
      if (! fromSet.contains(left))
        return false;
      if (! toSet.contains(right))
        return false;
      if (function_ || total_) {
        Expr to = map.get(left);
        if (to != null) {
          if (function_)
            return false;
        }
        else {
          map.put(left, right);
        }
      }
      if (onto_) range.add(right);
    }
    final int domSize = map.size();
    final int ranSize = range.size();
    if (total_ && domSize != fromSet.size())
      return false;
    if (onto_ && ranSize != toSet.size())
      return false;
    if (injective_ && domSize != ranSize)
      return false;
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

  /** This returns the function operator that has the given
   *  properties.  The resulting string is in email markup.
   */
  public static String funcName(boolean func, boolean inj,
      boolean tot, boolean onto)
  {
    StringBuffer result = new StringBuffer();
    if (! func)
      return "<-->";

    result.append(inj  ? ">"  : ""   );
    result.append(tot  ? "--" : "-|-");
    result.append(onto ? ">>" : ">"  );
    return result.toString();
  }

  public static String funcNameUnicode(boolean func, boolean inj,
      boolean tot, boolean onto)
  {
    String email = funcName(func, inj, tot, onto);
    if ("<-->".equals(email))
      return ZString.REL;
    if ("-|->>".equals(email))
      return ZString.PSURJ;
    if ("-|->".equals(email))
      return ZString.PFUN;
    if ("-->>".equals(email))
      return ZString.SURJ;
    if ("-->".equals(email))
      return ZString.FUN;
    //if (">-|->>".equals(email))
    //  return ZString.FINJ   is almost right, but finite-only
    if (">-|->".equals(email))
      return ZString.PINJ;
    if (">-->>".equals(email))
      return ZString.BIJ;
    if (">-->".equals(email))
      return ZString.INJ;
    throw new RuntimeException("There is no unicode for "+email);
  }

  /** This returns the function operator, in email markup. */
  public String funcName()
  {
    return funcName(function_, injective_, total_, onto_);
  }

  /** This returns the function operator, in Unicode markup. */
  public String funcNameUnicode()
  {
    return funcNameUnicode(function_, injective_, total_, onto_);
  }

  public String toString()
  {
    String func = funcName(function_, injective_, total_, onto_);
    return from_.toString() + " " + func + " " + to_.toString();
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof RelSetVisitor) {
      return ((RelSetVisitor<R>)visitor).visitRelSet(this);
    }
    return super.accept(visitor);
  }
}
