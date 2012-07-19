/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

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
package net.sourceforge.czt.animation.eval.result;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.ListIterator;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.Expr;

public class RangeSetTest extends ZTestCase
{
  private RangeSet empty1  = new RangeSet(BigInteger.ONE, BigInteger.ZERO);
  private RangeSet empty2  = new RangeSet(BigInteger.ZERO, BigInteger.valueOf(-10));
  private RangeSet nats    = new RangeSet(BigInteger.ZERO, null);
  private RangeSet upto3   = new RangeSet(null, BigInteger.valueOf(3));
  private RangeSet zero    = new RangeSet(BigInteger.ZERO, BigInteger.ZERO);
  private RangeSet zeroTo3 = new RangeSet(BigInteger.ZERO, BigInteger.valueOf(3));

  public void testEqualsObject()
  {
    assertEquals(empty1, empty2);
  }

  public void testGetLower()
  {
    assertEquals(BigInteger.ZERO, nats.getLower());
    assertEquals(null, upto3.getLower());
  }

  public void testGetUpper()
  {
    assertEquals(null, nats.getUpper());
    assertEquals(BigInteger.valueOf(3), upto3.getUpper());
  }

  public void testMaxSize()
  {
    assertEquals(BigInteger.ZERO, empty1.maxSize());
    assertEquals(BigInteger.ZERO, empty2.maxSize());
    assertEquals(null, nats.maxSize());
    assertEquals(null, upto3.maxSize());
    assertEquals(BigInteger.ONE, zero.maxSize());
    assertEquals(BigInteger.valueOf(4), zeroTo3.maxSize());
  }

  public void testEstSize()
  {
    assertEquals(0.0, empty1.estSize(), ACCURACY);
    assertEquals(EvalSet.INFINITE_SIZE, nats.estSize(), ACCURACY);
    assertEquals(EvalSet.INFINITE_SIZE, upto3.estSize(), ACCURACY);
    assertEquals(1.0, zero.estSize(), ACCURACY);
    assertEquals(4.0, zeroTo3.estSize(), ACCURACY);
  }

  public void testSize()
  {
    assertEquals(0, empty1.size());
    assertEquals(0, empty2.size());
    assertEquals(Integer.MAX_VALUE, nats.size());
    assertEquals(Integer.MAX_VALUE, upto3.size());
    assertEquals(1, zero.size());
    assertEquals(4, zeroTo3.size());
  }

  /** A helper method for testing an iterator. */
  private void from0To3(Iterator<Expr> iter)
  {
    assertTrue(iter.hasNext());
    assertEquals(i0, iter.next());
    assertTrue(iter.hasNext());
    assertEquals(i1, iter.next());
    assertTrue(iter.hasNext());
    assertEquals(i2, iter.next());
    assertTrue(iter.hasNext());
    assertEquals(i3, iter.next());
  }

  public void testIterator()
  {
    Iterator<Expr> iter = zeroTo3.iterator();
    from0To3(iter);
    assertFalse(iter.hasNext());
  }

  public void testIteratorEmpty()
  {
    Iterator<Expr> iter = empty1.iterator();
    assertFalse(iter.hasNext());
  }

  public void testSortedIterator()
  {
    Iterator<Expr> iter = zeroTo3.sortedIterator();
    from0To3(iter);
    assertFalse(iter.hasNext());
  }

  public void testListIterator()
  {
    ListIterator<Expr> iter = zeroTo3.listIterator();
    assertFalse(iter.hasPrevious());
    assertEquals(-1, iter.previousIndex());
    assertEquals(0, iter.nextIndex());
    from0To3(iter);
    assertFalse(iter.hasNext());
    assertEquals(4, iter.nextIndex());
    assertEquals(3, iter.previousIndex());
    assertTrue(iter.hasPrevious());
    assertEquals(i3, iter.previous());
    assertTrue(iter.hasPrevious());
    assertEquals(i2, iter.previous());
    assertEquals(2, iter.nextIndex());
    assertEquals(1, iter.previousIndex());
  }

  public void testListIteratorNats()
  {
    ListIterator<Expr> iter = nats.listIterator();
    assertFalse(iter.hasPrevious());
    assertEquals(-1, iter.previousIndex());
    assertEquals(0, iter.nextIndex());
    assertTrue(iter.hasNext());
    assertEquals(i0, iter.next());
    assertTrue(iter.hasNext());
    assertEquals(i1, iter.next());
    assertTrue(iter.hasNext());  // infinite nexts in fact
    assertEquals(2, iter.nextIndex());
    assertEquals(1, iter.previousIndex());
    assertTrue(iter.hasPrevious());
    assertEquals(i1, iter.previous());
    assertTrue(iter.hasPrevious());
    assertEquals(i0, iter.previous());
    assertFalse(iter.hasPrevious());
    assertEquals(0, iter.nextIndex());
    assertEquals(-1, iter.previousIndex());
  }

  public void testListIteratorUpto3()
  {
    ListIterator<Expr> iter = upto3.listIterator();
    assertFalse(iter.hasPrevious());
    assertEquals(-1, iter.previousIndex());
    assertEquals(0, iter.nextIndex());
    assertTrue(iter.hasNext());
    assertEquals(i3, iter.next());
    assertTrue(iter.hasNext());
    assertEquals(i2, iter.next());
    assertTrue(iter.hasNext()); // infinite nexts in fact
    assertEquals(2, iter.nextIndex());
    assertEquals(1, iter.previousIndex());
    assertTrue(iter.hasPrevious());
    assertEquals(i2, iter.previous());
    assertTrue(iter.hasPrevious());
    assertEquals(i3, iter.previous());
    assertFalse(iter.hasPrevious());
    assertEquals(0, iter.nextIndex());
    assertEquals(-1, iter.previousIndex());
  }

  public void testListIteratorEmpty()
  {
    ListIterator<Expr> iter = empty1.listIterator();
    assertFalse(iter.hasNext());
    assertEquals(0, iter.nextIndex());
    assertFalse(iter.hasPrevious());
    assertEquals(-1, iter.previousIndex());
  }

  public void testContains()
  {
    assertFalse(empty1.contains(i0));
    assertFalse(empty2.contains(i0));
    assertTrue(nats.contains(i0));
    assertFalse(nats.contains(in1));
    assertTrue(upto3.contains(i0));
    assertTrue(upto3.contains(i3));
    assertFalse(upto3.contains(i4));
    assertTrue(zero.contains(i0));
    assertFalse(zero.contains(i1));
    assertFalse(zero.contains(in1));
  }

  public void testContainsAll()
  {
    ArrayList<Expr> elems = new ArrayList<Expr>();
    elems.add(i0);
    elems.add(i3);
    assertTrue(zeroTo3.containsAll(elems));
    elems.add(i4);
    assertFalse(zeroTo3.containsAll(elems));
  }

  public void testIsEmpty()
  {
    assertTrue(empty1.isEmpty());
    assertTrue(empty2.isEmpty());
    assertFalse(nats.isEmpty());
    assertFalse(upto3.isEmpty());
    assertFalse(zero.isEmpty());
  }

  public void testIsFinite()
  {
    assertTrue(empty1.isFinite());
    assertTrue(empty2.isFinite());
    assertFalse(nats.isFinite());
    assertFalse(upto3.isFinite());
    assertTrue(zero.isFinite());
  }

  public void testUnionRangeSet()
  {
    assertEquals(zeroTo3, zeroTo3.union(empty2));
    assertEquals(nats, zeroTo3.union(new RangeSet(BigInteger.valueOf(10),null)));
    assertEquals(zeroTo3, zero.union(zeroTo3));
    assertEquals(upto3, zero.union(upto3));
    assertEquals(new RangeSet(null, null), nats.union(upto3));
  }

  public void testUnionBigIntegerBigInteger()
  {
    assertEquals(nats, zeroTo3.union(BigInteger.valueOf(10),null));
  }

  public void testIntersectRangeSet()
  {
    assertEquals(empty1, zeroTo3.intersect(empty2));
    assertEquals(empty1, zeroTo3.intersect(new RangeSet(BigInteger.valueOf(4),null)));
    assertEquals(zero, zero.intersect(zeroTo3));
    assertEquals(zeroTo3, nats.intersect(upto3));
    assertEquals(zeroTo3, new RangeSet(null, null).intersect(zeroTo3));
    assertEquals(nats, new RangeSet(null, null).intersect(nats));
    assertEquals(upto3, new RangeSet(null, null).intersect(upto3));
  }

  public void testIntersectBigIntegerBigInteger()
  {
    assertEquals(empty1, zeroTo3.intersect(BigInteger.valueOf(4),null));
  }

  public void testHashCode()
  {
    assertEquals(empty1.hashCode(), empty2.hashCode());
  }

  public void testEstSubsetSize()
  {
    assertEquals(EvalSet.INFINITE_SIZE, upto3.estSubsetSize(new Envir(), x), ACCURACY);
    assertEquals(4.0, zeroTo3.estSubsetSize(new Envir(), x), ACCURACY);
  }

  public void testSubsetIterator()
  {
    Iterator<Expr> iter = nats.subsetIterator(upto3);
    from0To3(iter);
    assertFalse(iter.hasNext());
  }

  public void testToString()
  {
    assertEquals("0..3", zeroTo3.toString());
    assertEquals("_..3", upto3.toString());
    assertEquals("0.._", nats.toString());
  }

}
