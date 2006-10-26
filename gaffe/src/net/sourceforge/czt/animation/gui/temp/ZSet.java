/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.temp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatDiscreteSet;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
 * Values in Z that are Sets.
 */
public class ZSet implements ZValue
{
  // private final Vector set_;
  private final EvalSet expr_;

  private final Factory factory_;

  private Envir env_;

  private int i = 0;

  private List<ZName> list;

  // private static Factory factory;
  /**
   * Construct an empty <code>ZSet</code>.
   */
  public ZSet()
  {
    this(new HashSet<ZValue>());
  }

  /**
   * Construct a <code>ZSet</code> from a <code>Set</code> of values.
   * 
   * @param set
   *            The set to store.
   */
  public ZSet(Set<? extends ZValue> set)
  {
    // set_ = new Vector(set);
    env_ = new Envir();
    list = new ArrayList<ZName>();
    factory_ = GaffeFactory.getFactory();
    ZName setName = factory_.createZName("NoName");
    ZName tempName = null;
    for (ZValue zValue : set) {
      tempName = factory_.createZName(String.valueOf(i++));
      env_ = env_.plus(tempName, zValue.getExpr());
      list.add(tempName);
    }
    env_ = env_.plus(setName, null);
    FlatDiscreteSet s = new FlatDiscreteSet(list, setName);
    s.inferBounds(new Bounds());
    Mode m = s.chooseMode(env_);
    s.setMode(m);
    s.startEvaluation();
    s.nextEvaluation();
    expr_ = s;
  }

  /**
   * Construct a <code>ZSet</code> by a <code>EvalSet</code> expr
   * 
   * @param expr_
   *            The <code>EvalSet</code> expr to store
   */
  public ZSet(EvalSet expr)
  {
    this.expr_ = expr;
    factory_ = GaffeFactory.getFactory();
  }

  /**
   * Dynamiclly wrapping the memember of Expr to ZValue
   * 
   * @author Mark Utting
   */
  public class ZSetIterator implements ListIterator<ZValue>
  {
    ListIterator<Expr> exprs;

    public ZSetIterator(ListIterator<Expr> expr_)
    {
      this.exprs = expr_;
    }

    public boolean hasNext()
    {
      return exprs.hasNext();
    }

    public ZValue next()
    {
      ZValue result = null;
      try {
        result = GaffeFactory.zValue(exprs.next());
      } catch (UnexpectedTypeException ute) {
        ute.printStackTrace();
      }
      return result;
    }

    public boolean hasPrevious()
    {
      return exprs.hasPrevious();

    }

    public ZValue previous()
    {
      ZValue result = null;
      try {
        result = GaffeFactory.zValue(exprs.previous());
      } catch (UnexpectedTypeException ute) {
        ute.printStackTrace();
      }
      return result;
    }

    public int nextIndex()
    {
      return exprs.nextIndex();
    }

    public int previousIndex()
    {
      return exprs.previousIndex();
    }

    public void set(ZValue arg0)
    {
      exprs.set(arg0.getExpr());
    }

    public void add(ZValue arg0)
    {
      exprs.add(arg0.getExpr());
    }

    public void remove()
    {
      exprs.remove();
    }
  }

  /**
   * @return An iterator over this <code>ZSet</code>.
   */
  public ListIterator<ZValue> iterator()
  {
    // return set_.iterator();
    return new ZSetIterator(expr_.listIterator());
  }

  /**
   * @return The set's size.
   */
  public int size()
  {
    // return set_.size();
    int result = 0;
    for (Iterator<Expr> it = expr_.iterator(); it.hasNext();) {
      it.next();
      result++;
    }
    return result;
  }

  /**
   * @param value
   *            A value to look for in this <code>ZSet</code>.
   * @return <code>true</code> if the <code>ZSet</code> contains
   *         <code>value</code>.
   */
  public boolean contains(ZValue value)
  {
    // return set_.contains(value);
    return expr_.contains(value.getExpr());
  }

  /**
   * @param index
   *            An index into the set.
   * @return The <code>index</code>th value in the set.
   */
  public ZValue get(int index)
  {
    // return (ZValue) set_.get(index);
    ZValue result = null;
    try {
      result = GaffeFactory.zValue(expr_.getEnvir().lookup(
          GaffeFactory.getFactory().createZName(String.valueOf(index))));
    } catch (UnexpectedTypeException ute) {
      ute.printStackTrace();
    }
    return result;
  }

  /**
   * @return This <code>ZSet</code> translated into a <code>Set</code>.
   */
  public Set<ZValue> getSet()
  {
    // return new HashSet(set_);
    Set<ZValue> result = new HashSet<ZValue>();
    for (Iterator<Expr> it = expr_.iterator(); it.hasNext();) {
      try {
        result.add(GaffeFactory.zValue(it.next()));
      } catch (UnexpectedTypeException ute) {
        ute.printStackTrace();
      }
    }
    return result;
  }

  /**
   * @return A string representation of this set.
   */
  public String toString()
  {
    // String result = "ZSet: { ";
    // Iterator it = iterator();
    // if (it.hasNext()) result += it.next();
    // while (it.hasNext()) result += " , " + it.next();
    // result += " }";
    // return result;
    return expr_.toString();
  }

  /**
   * Compare for equality against another object.
   * 
   * @param obj
   *            The object to compare against.
   * @return <code>true</code> if <code>obj</code> is a <code>ZSet</code>
   *         containing all of the same values as this one.
   */
  public boolean equals(Object obj)
  {
    // return obj instanceof ZSet && ((ZSet) obj).set_.equals(set_);
    return expr_.equals(((ZValue) obj).getExpr());
  }

  /**
   * @return This object's hashcode.
   */
  public int hashCode()
  {
    // return set_.hashCode();
    return expr_.hashCode();
  }

  /**
   * Get the expr type representing the zvalue
   * 
   * @return the representing expr
   */
  public EvalSet getExpr()
  {
    return expr_;
  }
}
