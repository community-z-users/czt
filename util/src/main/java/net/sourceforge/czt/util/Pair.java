/*
  Copyright (C) 2007 Mark Utting
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

package net.sourceforge.czt.util;

import java.util.ArrayList;
import java.util.List;

/**
 * A pair of objects.
 *
 * @param <T1> type of the first object.
 * @param <T2> type of the second object.
 * @author leo
 */
public class Pair<T1, T2>
{
  private final T1 first_;
  private final T2 second_;

  /** Creates a new instance of NodePair. Use the static factory for construction. Use this constructor for extension.
   * @param e1
   * @param e2
   */
  protected Pair(T1 e1, T2 e2)
  {
    if (e1 == null || e2 == null) throw new NullPointerException();
    first_ = e1;
    second_ = e2;
  }

  /**
   *
   * @param <A>
   * @param <B>
   * @param first
   * @param second
   * @return
   */
  public static <A, B> Pair<A, B> getPair(A first, B second)
  {
    return new Pair<A, B>(first, second);
  }

  public static <A, B> List<Pair<A, B>> getPairList(A first, B second)
  {
    List<Pair<A, B>> result = new ArrayList<Pair<A, B>>(1);
    result.add(getPair(first, second));
    return result;
  }

  @Override
  public String toString()
  {
    return "( " + first_ + ", " + second_ + " )";
  }

  @Override
  public int hashCode()
  {
    return first_.hashCode() + second_.hashCode();
  }

  @Override
  public boolean equals(Object o)
  {
    if (o == null) return false;
    else if (o instanceof Pair<?, ?>) {
      Pair<?, ?> p = (Pair<?, ?>) o;
      return (first_.equals(p.first_) && second_.equals(p.second_));
    }
    else return false;
  }

  public T1 getFirst()
  {
    return first_;
  }

  public T2 getSecond()
  {
    return second_;
  }
}
