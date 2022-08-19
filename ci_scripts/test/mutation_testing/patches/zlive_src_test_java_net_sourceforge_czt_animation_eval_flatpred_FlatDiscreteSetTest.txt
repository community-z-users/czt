/**
Copyright (C) 2004 Mark Utting
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

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.EvalSetTest;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing FlatDiscreteSet.
 *
 * @author Mark Utting
 */
public class FlatDiscreteSetTest
  extends EvalSetTest
{
  /** This overrides set and emptySet to be FlatDiscreteSet objects.
   *  set = {i,k,j,i} and emptySet = {}.
   */
  public FlatDiscreteSetTest()
  {
  }

  public void setUp()
  {
    super.setUp();
    ArrayList<ZName> argsList = new ArrayList<ZName>();
    argsList.add(i);
    argsList.add(k);
    argsList.add(j);
    argsList.add(i);
    set = new FlatPredList(zlive_);
    set.add(new FlatDiscreteSet(argsList,s));
    set.inferBoundsFixPoint(bounds_);

    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatDiscreteSet(new ArrayList<ZName>(),es));
    emptySet.inferBoundsFixPoint(bounds_);
  }

  public void testToString()
  {
    // WARNING: the order of names may depend upon HashSet ordering.
    assertEquals("s = { i, j, k }", set.toString());
    assertEquals("es = {  }", emptySet.toString());
  }

  /** Tests the static bounds inference. */
  public void testMaxSize()
  {
    EvalSet resultSet = bounds_.getEvalSet(s);
    Assert.assertNotNull(resultSet);
    Assert.assertTrue(resultSet instanceof FuzzySet);
    Assert.assertEquals(BigInteger.valueOf(3), resultSet.maxSize());
    Assert.assertEquals(3.0, resultSet.estSize(), ACCURACY);
    Assert.assertEquals(null, resultSet.getLower());
    Assert.assertEquals(null, resultSet.getUpper());
    
    // now with tighter bounds
    setIJKBounds();
    set.inferBoundsFixPoint(bounds_);
    resultSet = bounds_.getEvalSet(s);
    Assert.assertNotNull(resultSet);
    Assert.assertTrue(resultSet instanceof FuzzySet);
    Assert.assertEquals(BigInteger.valueOf(3), resultSet.maxSize());
    Assert.assertEquals(3.0, resultSet.estSize(), ACCURACY);
    Assert.assertEquals(BigInteger.valueOf(10), resultSet.getLower());
    Assert.assertEquals(BigInteger.valueOf(12), resultSet.getUpper());
  }
}




