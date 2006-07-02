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
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.util.Factory;

//import java.util.Vector;

/**
 * Class representing Z values that are Tuples.
 */
public class ZTuple implements ZValue
{
  //private Vector tuple_;
  private TupleExpr e;

  private static Factory factory;

  /**
   * Construct an empty tuple.
   * Not possible in Z, intended for the convenience of code using ZTuples.
   */
  public ZTuple()
  {
    //tuple_ = new Vector();
    factory = GaffeFactory.getFactory();
    e = factory.createTupleExpr();
  }

  /**
   * Construct a tuple containing two values.
   * @param a The first value.
   * @param b The second value.
   */
  public ZTuple(ZValue a, ZValue b)
  {
    //tuple_ = new Vector();
    //tuple_.add(a);
    //tuple_.add(b);
    factory = GaffeFactory.getFactory();
    e = factory.createTupleExpr(a.getExpr(), b.getExpr());
  }

  /**
   * Construct a tuple from a list of values.
   * @param tuple The list of values.
   */
  public ZTuple(List<ZValue> tuple)
  {
    //tuple_ = new Vector(tuple);
    factory = GaffeFactory.getFactory();
    List<Expr> exprTuple = new ArrayList<Expr>();
    for (ZValue zValue : tuple) {
      exprTuple.add(zValue.getExpr());
    }
    e = factory.createTupleExpr(factory.createZExprList(exprTuple));
  }

  /**
   * Construct a <code>ZTuple</code> by a given <code>TupleExpr</code>
   * @param e The <code>TupleExpr</code> to store
   */
  public ZTuple(TupleExpr e)
  {
    this.e = e;
  }

  /**
   * Dynamiclly wrapping the memember of Expr to ZValue
   * @author Mark Utting
   */
  public class ZTupleIterator implements Iterator<ZValue>
  {
    Iterator<Expr> exprs;

    public ZTupleIterator(Iterator<Expr> e)
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
        result = GaffeFactory.zValue(exprs.next());
      } catch (UnexpectedTypeException ute) {
        ute.printStackTrace();
      }
      return result;
    }

    public void remove()
    {
      throw new UnsupportedOperationException();
    }
  }

  /**
   * @return An iterator over the values in the tuple.
   */
  public Iterator iterator()
  {
    //return tuple_.iterator();
    return new ZTupleIterator(e.getZExprList().iterator());
  }

  /**
   * @return The number of values in the tuple.
   */
  public int size()
  {
    //return tuple_.size();
    return e.getZExprList().size();
  }

  /**
   * Return the <code>index</code>th value in the tuple.
   * @param index Index into the tuple.
   * @return The value at location <code>index</code>.
   */
  public ZValue get(int index)
  {
    //return (ZValue) tuple_.get(index);
    ZValue result = null;
    try {
      result = GaffeFactory.zValue(e.getZExprList().get(index));
    } catch (UnexpectedTypeException ute) {
      ute.printStackTrace();
    }
    return result;
  }

  /**
   * @return a <code>String</code> representation of the tuple.
   */
  public String toString()
  {
    //String result = "( ";
    //Iterator it = iterator();
    //if (it.hasNext()) result += it.next();
    //while (it.hasNext()) result += " , " + it.next();
    //result += " )";
    //return result;
    return e.toString();
  }

  /**
   * Test equality with another object.
   * @param obj The object to compare against.
   * @return <code>true</code> if obj is a tuple with the same values in the
   *         same order.
   */
  public boolean equals(Object obj)
  {
    //return obj instanceof ZTuple && ((ZTuple) obj).tuple_.equals(tuple_);
    return e.equals(((ZValue) obj).getExpr());
  }

  /**
   * @return this object's hashcode.
   */
  public int hashCode()
  {
    //return tuple_.hashCode();
    return e.hashCode();
  }

  /**
   * Get the expr type representing the zvalue
   * @return the representing expr
   */
  public Expr getExpr()
  {
    return e;
  }
}
