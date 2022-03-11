/**
Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.animation.eval.flatpred;

import java.math.BigInteger;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalSetTest;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing FlatDiscreteSet.
 *
 * @author Mark Utting
 */
public class FlatRangeSetTest
  extends EvalSetTest
{
  /** This overrides set and emptySet to be FlatRangeSet objects.
   *  set = 10..12 and emptySet = 12..11.
   */
  public FlatRangeSetTest()
  {
  }

  public void setUp()
  {
    super.setUp();
    set = new FlatPredList(zlive_);
    set.add(new FlatRangeSet(i,k,s));   // 10..12
    set.inferBoundsFixPoint(bounds_);

    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatRangeSet(k,j,es));   // 12..11
    emptySet.inferBoundsFixPoint(bounds_);
  }

  /** A helper function for constructing and evaluating RangeSets. */
  private EvalSet range(ZName lo, ZName hi, Envir env)
  {
    FlatRangeSet flat1 = new FlatRangeSet(lo,hi,s);
    flat1.inferBounds(new Bounds(null));  // empty bounds
    Mode m1 = flat1.chooseMode(env);
    Assert.assertNotNull(m1);
    flat1.setMode(m1);
    flat1.startEvaluation();
    Assert.assertTrue(flat1.nextEvaluation());
    Expr e = flat1.getEnvir().lookup(s);
    assertNotNull(e);
    assertTrue(e instanceof RangeSet);
    return (RangeSet) e;
  }

  public void testNoBoundEquality()
  {
    EvalSet set = range(null,null,envIJK);
    Assert.assertTrue(set.equals(range(null, null, envI)));
    EvalSet other = range(i,null,envIJK);
    boolean result = set.equals(other);
    Assert.assertFalse(result);
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(i,j,envIJK)));
  }

  public void testLowerBoundEquality()
  {
    EvalSet set = range(j,null,envIJK); // 11..infinity
    Assert.assertTrue(set.equals(range(j,null,envJ)));
    Assert.assertFalse(set.equals(range(i,null,envIJK)));
    Assert.assertFalse(set.equals(range(k,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(j,k,envIJK)));
  }

  public void testUpperBoundEquality()
  {
    EvalSet set = range(null,j,envIJK); // -infinity..11
    Assert.assertTrue(set.equals(range(null,j,envJ)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(null,k,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(j,null,envIJK)));
    Assert.assertFalse(set.equals(range(j,k,envIJK)));
  }

  public void testEmptyEquality()
  {
    EvalSet set = range(j,i,envIJK); // 11..10
    Assert.assertTrue(set.equals(range(k,j,envIJK)));  // 12..11
    Assert.assertFalse(set.equals(range(j,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(i,j,envIJK))); // 10..11
    Assert.assertFalse(set.equals(range(j,j,envIJK))); // 11..11
    Assert.assertFalse(set.equals(range(i,i,envIJK))); // 10..10
    Assert.assertEquals(BigInteger.valueOf(0), set.maxSize());
  }

  public void testOrdinaryEquality()
  {
    EvalSet set = range(i,k,envIJK); // 10..12
    Assert.assertTrue(set.equals(range(i,k,envIJK)));
    Assert.assertFalse(set.equals(range(i,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,k,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(i,j,envIJK))); // 10..11
    Assert.assertFalse(set.equals(range(j,k,envIJK))); // 11..12
    Assert.assertEquals(BigInteger.valueOf(3), set.maxSize());
  }

  public void testToString()
  {
    assertEquals("s = i .. k", set.toString());
  }
}




