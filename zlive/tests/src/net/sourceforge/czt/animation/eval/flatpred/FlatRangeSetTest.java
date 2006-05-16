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
import net.sourceforge.czt.z.ast.ZRefName;


/**
 * A (JUnit) test class for testing FlatDiscreteSet.
 *
 * @author Mark Utting
 */
public class FlatRangeSetTest
  extends EvalSetTest
{
  /** This overrides set and emptySet to be FlatDiscreteSet objects.
   *  set = {i,k,j,i} and emptySet = {}.
   */
  public FlatRangeSetTest()
  {
  }

  public void setUp()
  {
    set = new FlatPredList(zlive_);
    set.add(new FlatRangeSet(i,k,s));   // 10..12
    set.inferBounds(new Bounds());

    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatRangeSet(k,j,s));   // 12..11
    emptySet.inferBounds(new Bounds());
  }

  /** A helper function for constructing and evaluating FlatRangeSets. */
  private FlatRangeSet range(ZRefName lo, ZRefName hi, Envir env)
  {
    FlatRangeSet flat1 = new FlatRangeSet(lo,hi,s);
    Mode m1 = flat1.chooseMode(env);
    Assert.assertNotNull(m1);
    flat1.setMode(m1);
    flat1.startEvaluation();
    Assert.assertTrue(flat1.nextEvaluation());
    return flat1;
  }

  public void testNoBoundEquality()
  {
    FlatRangeSet set = range(null,null,envIJK);
    Assert.assertTrue(set.equals(range(null, null, envI)));
    Assert.assertFalse(set.equals(range(i,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(i,j,envIJK)));
    Assert.assertNull(set.maxSize());
  }

  public void testLowerBoundEquality()
  {
    FlatRangeSet set = range(j,null,envIJK); // 11..infinity
    Assert.assertTrue(set.equals(range(j,null,envJ)));
    Assert.assertFalse(set.equals(range(i,null,envIJK)));
    Assert.assertFalse(set.equals(range(k,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(j,k,envIJK)));
    Assert.assertNull(set.maxSize());
  }

  public void testUpperBoundEquality()
  {
    FlatRangeSet set = range(null,j,envIJK); // -infinity..11
    Assert.assertTrue(set.equals(range(null,j,envJ)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(null,k,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(j,null,envIJK)));
    Assert.assertFalse(set.equals(range(j,k,envIJK)));
    Assert.assertNull(set.maxSize());
  }

  public void testEmptyEquality()
  {
    FlatRangeSet set = range(j,i,envIJK); // 11..10
    Assert.assertTrue(set.equals(range(k,j,envIJK)));  // 12..11
    Assert.assertFalse(set.equals(range(j,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,i,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(i,j,envIJK))); // 10..11
    Assert.assertFalse(set.equals(range(j,j,envIJK))); // 11..11
    Assert.assertFalse(set.equals(range(i,i,envIJK))); // 10..10
    Assert.assertEquals(new BigInteger("0"), set.maxSize());
  }

  public void testOrdinaryEquality()
  {
    FlatRangeSet set = range(i,k,envIJK); // 10..12
    Assert.assertTrue(set.equals(range(i,k,envIJK)));
    Assert.assertFalse(set.equals(range(i,null,envIJK)));
    Assert.assertFalse(set.equals(range(null,k,envIJK)));
    Assert.assertFalse(set.equals(range(null,null,envIJK)));
    Assert.assertFalse(set.equals(range(i,j,envIJK))); // 10..11
    Assert.assertFalse(set.equals(range(j,k,envIJK))); // 11..12
    Assert.assertEquals(new BigInteger("3"), set.maxSize());
  }
}




