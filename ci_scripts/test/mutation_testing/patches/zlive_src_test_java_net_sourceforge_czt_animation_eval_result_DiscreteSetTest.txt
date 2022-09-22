/**
Copyright (C) 2007 Mark Utting
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
import java.util.Iterator;

import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.Expr;

/**
 * A simple implementation of a power set.
 *
 * @author Mark Utting
 */
public class DiscreteSetTest extends ZTestCase
{
  public void testEmpty()
  {
    DiscreteSet set = new DiscreteSet();
    assertEquals("{}", set.toString());
    assertTrue(set.isEmpty());
    assertEquals(0.0, set.estSize(), ACCURACY);
    assertEquals(BigInteger.ZERO, set.maxSize());
    assertEquals(0, set.size());
    assertFalse(set.contains(i1));
    Iterator<Expr> iter = set.iterator();
    assertFalse(iter.hasNext());
  }

  public void testNonEmpty()
  {
    DiscreteSet set = new DiscreteSet();
    set.add(i1);
    set.add(i3);
    set.add(i1);
    assertEquals("{1, 3}", set.toString());
    assertFalse(set.isEmpty());
    assertEquals(2.0, set.estSize(), ACCURACY);
    assertEquals(BigInteger.valueOf(2), set.maxSize());
    assertEquals(2, set.size());
    assertTrue(set.contains(i1));
    assertFalse(set.contains(i2));
    assertTrue(set.contains(i3));
    Iterator<Expr> iter = set.iterator();
    assertTrue(iter.hasNext());
    assertNotNull(iter.next());
    assertTrue(iter.hasNext());
    assertNotNull(iter.next());
    assertFalse(iter.hasNext());
    assertEquals(BigInteger.valueOf(1), set.getLower());
    assertEquals(BigInteger.valueOf(3), set.getUpper());
  }
}
