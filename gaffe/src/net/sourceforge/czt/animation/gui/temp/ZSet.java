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
import net.sourceforge.czt.animation.eval.flatpred.FlatDiscreteSet;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;

/**
 * Values in Z that are Sets.
 */
public class ZSet implements ZValue
{
  // private final Vector set_;
  private final EvalSet e;

  private Envir env;

  private int i = 0;

  private List<ZRefName> list;

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
    env = new Envir();
    list = new ArrayList<ZRefName>();
    ZRefName setName = ZFactory.getFactory().createZRefName("NoName");
    ZRefName tempName = null;
    for (ZValue zValue : set) {
      tempName = ZFactory.getFactory().createZRefName(String.valueOf(i++));
      env = env.plus(tempName, zValue.getExpr());
      list.add(tempName);
    }
    env = env.plus(setName, null);
    FlatDiscreteSet s = new FlatDiscreteSet(list, setName);
    Mode m = s.chooseMode(env);
    s.setMode(m);
    s.startEvaluation();
    s.nextEvaluation();
    e = s;
  }

  /**
   * Construct a <code>ZSet</code> by a <code>EvalSet</code> expr
   * 
   * @param e
   *            The <code>EvalSet</code> expr to store
   */
  public ZSet(EvalSet e)
  {
    this.e = e;
  }

  public void add(ZValue value)
  {
    ZRefName tempName = ZFactory.getFactory().createZRefName(
        String.valueOf(i++));
    this.env = env.plus(tempName, value.getExpr());
  }

  /**
   * Dynamiclly wrapping the memember of Expr to ZValue
   * 
   * @author Mark Utting
   */
  public class ZSetIterator implements ListIterator<ZValue>
  {
    ListIterator<Expr> exprs;

    public ZSetIterator(ListIterator<Expr> e)
    {
      this.exprs = e;
    }

    public boolean hasNext()
    {
      return exprs.hasNext();
    }

    public ZValue next()
    {
      ZValue result = null;
      try {
        result = ZFactory.zValue(exprs.next());
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
        result = ZFactory.zValue(exprs.previous());
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
  public ListIterator iterator()
  {
    // return set_.iterator();
    return new ZSetIterator(e.listIterator());
  }

  /**
   * @return The set's size.
   */
  public int size()
  {
    // return set_.size();
    int result = 0;
    for (Iterator<Expr> it = e.iterator(); it.hasNext();) {
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
    return e.contains(value.getExpr());
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
      result = ZFactory.zValue(e.getEnvir().lookup(
          ZFactory.getFactory().createZRefName(String.valueOf(index))));
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
    for (Iterator<Expr> it = e.iterator(); it.hasNext();) {
      try {
        result.add(ZFactory.zValue(it.next()));
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
    return e.toString();
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
    return e.equals(((ZValue) obj).getExpr());
  }

  /**
   * @return This object's hashcode.
   */
  public int hashCode()
  {
    // return set_.hashCode();
    return e.hashCode();
  }

  /**
   * Get the expr type representing the zvalue
   * 
   * @return the representing expr
   */
  public Expr getExpr()
  {
    return e;
  }
}
