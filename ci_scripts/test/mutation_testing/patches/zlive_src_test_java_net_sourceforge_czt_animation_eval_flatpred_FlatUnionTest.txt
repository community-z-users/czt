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
import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.EvalSetTest;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing FlatUnion.
 *
 * @author Mark Utting
 */
public class FlatUnionTest
  extends EvalSetTest
{
  FlatUnion union;
  FlatUnion emptyUnion;
  ZName s1, s2;
  
  /** This overrides set and emptySet to be FlatUnionSet objects.
   *  set = {i,k,j,i} and emptySet = {}.
   */
  public FlatUnionTest()
  {
  }

  public void setUp()
  {
    super.setUp();
    s1 = zlive_.createNewName();
    s2 = zlive_.createNewName();
    set = new FlatPredList(zlive_);
    set.add(new FlatRangeSet(i,j,s1));   // 10..11
    List<ZName> jk = new ArrayList<ZName>();
    jk.add(j);
    jk.add(k);
    jk.add(j);
    set.add(new FlatDiscreteSet(jk,s2));   // 11..12
    union = new FlatUnion(s1,s2,s);
    set.add(union);
    set.inferBoundsFixPoint(bounds_);

    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatRangeSet(k,j,s1));   // 12..11
    emptySet.add(new FlatDiscreteSet(new ArrayList<ZName>(), s2));
    emptyUnion = new FlatUnion(s1,s2,es);
    emptySet.add(emptyUnion);
    emptySet.inferBoundsFixPoint(bounds_);
  }

  public void testToString()
  {
    assertEquals("s = "+s1+" u "+s2, union.toString());
  }

  public void testEmptyBounds()
  {
    // set some real bounds on i,j,k.
    setIJKBounds();
    // TODO: this should give true once we infer bounds of sets of integers.
    //Assert.assertTrue(emptySet.inferBounds(bounds_));
    emptySet.inferBounds(bounds_);
    Assert.assertNull(emptyUnion.getLower());
    Assert.assertNull(emptyUnion.getUpper());
  }

  public void testBounds()
  {
    // set some real bounds on i,j,k.
    setIJKBounds();
    // TODO: this should give true once we infer bounds of sets of integers.
    //Assert.assertTrue(set.inferBounds(bounds_));
    set.inferBounds(bounds_);
    Assert.assertEquals(new BigInteger("10"), union.getLower());
    Assert.assertEquals(new BigInteger("12"), union.getUpper());
  }
}




