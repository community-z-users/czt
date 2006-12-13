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
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.util.Factory;

/**
 * A simple implementation of a power set.
 *
 * @author Petra Malik
 */
public class PowerSetTest extends ZTestCase
{
  public void testEmpty()
  {
    PowerSet powerSet = new PowerSet(new DiscreteSet());
    assertFalse(powerSet.isEmpty());
    assertEquals(1.0, powerSet.estSize(), ACCURACY);
    assertEquals(BigInteger.ONE, powerSet.maxSize());
    assertEquals(1, powerSet.size());
    assertTrue(powerSet.contains(new DiscreteSet()));
    Iterator<Expr> iter = powerSet.iterator();
    assertTrue(iter.hasNext());
    assertEquals(new DiscreteSet(), iter.next());
    assertFalse(iter.hasNext());
  }

  public void testOneElement()
  {
    DiscreteSet baseSet = new DiscreteSet();
    baseSet.add(i3);
    PowerSet powerSet = new PowerSet(baseSet);
    assertFalse(powerSet.isEmpty());
    assertEquals(2.0, powerSet.estSize(), ACCURACY);
    assertEquals(BigInteger.valueOf(2), powerSet.maxSize());
    assertEquals(2, powerSet.size());
    assertTrue(powerSet.contains(new DiscreteSet()));
    assertTrue(powerSet.contains(baseSet));
    Iterator<Expr> iter = powerSet.iterator();
    assertTrue(iter.hasNext());
    assertEquals(new DiscreteSet(), iter.next());
    assertTrue(iter.hasNext());
    assertEquals(baseSet, iter.next());
    assertFalse(iter.hasNext());
  }
}
