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

import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.Expr;

/**
 * Tests for PowerSet.
 *
 * @author Petra Malik
 */
public class ProdSetTest extends ZTestCase
{
  public void testSimpleEmpty()
  {
    List<EvalSet> basesets = new ArrayList<EvalSet>();
    DiscreteSet emptySet = new DiscreteSet();
    assertEquals(BigInteger.ZERO, emptySet.maxSize());
    basesets.add(emptySet);
    ProdSet prodSet = new ProdSet(basesets);
    assertTrue(prodSet.isEmpty());
    assertEquals(BigInteger.ZERO, prodSet.maxSize());
    assertEquals(0.0, prodSet.estSize(), ACCURACY);
    assertEquals(0, prodSet.size());
    Iterator<Expr> iter = prodSet.iterator();
    assertFalse(iter.hasNext());
  }

  public void testEmpty()
  {
    List<EvalSet> basesets = new ArrayList<EvalSet>();
    basesets.add(getSet1());
    basesets.add(getEmptySet());
    basesets.add(getSet2());
    ProdSet prodSet = new ProdSet(basesets);
    assertTrue(prodSet.isEmpty());
    assertEquals(BigInteger.ZERO, prodSet.maxSize());
    assertEquals(0.0, prodSet.estSize(), ACCURACY);
    assertEquals(0, prodSet.size());
    Iterator<Expr> iter = prodSet.iterator();
    assertFalse(iter.hasNext());
  }

  public void testSimple1()
  {
    List<EvalSet> basesets = new ArrayList<EvalSet>();
    DiscreteSet set = new DiscreteSet();
    set.add(i3);
    basesets.add(set);
    basesets.add(set);
    ProdSet prodSet = new ProdSet(basesets);
    assertFalse(prodSet.isEmpty());
    assertEquals(BigInteger.valueOf(1), prodSet.maxSize());
    assertEquals(1.0, prodSet.estSize(), ACCURACY);
    assertEquals(1, prodSet.size());
    Iterator<Expr> iter = prodSet.iterator();
    assertTrue(iter.hasNext());
    assertTrue(prodSet.contains(iter.next()));
    assertFalse(iter.hasNext());
  }

  public void testSimple2()
  {
    List<EvalSet> basesets = new ArrayList<EvalSet>();
    basesets.add(getSet1());
    basesets.add(getSet2());
    ProdSet prodSet = new ProdSet(basesets);
    assertFalse(prodSet.isEmpty());
    assertEquals(BigInteger.valueOf(2), prodSet.maxSize());
    assertEquals(2.0, prodSet.estSize(), ACCURACY);
    assertEquals(2, prodSet.size());
    Iterator<Expr> iter = prodSet.iterator();
    assertTrue(iter.hasNext());
    assertTrue(prodSet.contains(iter.next()));
    assertTrue(iter.hasNext());
    assertTrue(prodSet.contains(iter.next()));
    assertFalse(iter.hasNext());
  }

  private DiscreteSet getEmptySet()
  {
    return new DiscreteSet();
  }

  private DiscreteSet getSet1()
  {
    DiscreteSet result = new DiscreteSet();
    result.add(i1);
    return result;
  }

  private DiscreteSet getSet2()
  {
    DiscreteSet result = new DiscreteSet();
    result.add(i2);
    result.add(i3);
    return result;
  }
}
