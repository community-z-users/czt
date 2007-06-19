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

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the FlatMember class.
 *
 * @author Mark Utting
 */
public class FlatMemberTest
  extends ZTestCase
{
  private NumExpr i40 = factory_.createNumExpr(40);
  private ZName w = factory_.createZName("w");

  private FlatRangeSet set;
  private FlatMember mem;
  private FlatPredList predlist;

  protected void setUp()
  {
    set = new FlatRangeSet(x,y,z);
    mem = new FlatMember(z,w);  // w \in z

    // Must set up a flatpred list and do the static inference
    // pass before we can start using FlatRangeSet.
    predlist = new FlatPredList(zlive_);
    predlist.add(set);
    predlist.add(mem);
    predlist.inferBoundsFixPoint(new Bounds(null));
  }

  public void testToString()
  {
    assertEquals("w in z :: 100.0 ", mem.toString());
  }

  public void testEmpty()
  {
    Mode m = mem.chooseMode(empty);
    Assert.assertNull(m);
  }

  public void testOI()
  {
    Envir env = empty.plus(w,i20);
    Mode m = mem.chooseMode(env);
    Assert.assertNull(m);
  }

  /** Test 20 \in 10..40  and 5 \notin 10..40. */
  public void testII()
  {
    Envir env = empty.plus(x,i10);
    env = env.plus(y,i40);
    env = env.plus(w,i20);
    Mode setMode = set.chooseMode(env);
    Assert.assertTrue(setMode != null);
    Mode memMode = mem.chooseMode(setMode.getEnvir());
    Assert.assertTrue(memMode != null);
    Assert.assertEquals("result value", i20, memMode.getEnvir().lookup(w));
    // start the set evaluation first
    set.setMode(setMode);
    set.startEvaluation();
    Assert.assertTrue(set.nextEvaluation());
    // Start an Evaluation which succeeds. 20 in 10..40
    mem.setMode(memMode);
    mem.startEvaluation();
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertFalse(mem.nextEvaluation());
    //Start an Evaluation which fails. 5 in 10..40
    memMode.getEnvir().setValue(w,i5);
    mem.startEvaluation();
    Assert.assertFalse(mem.nextEvaluation());
  }

  /** Test w \in 10..15. */
  public void testIO()
  {
    Envir env = empty.plus(x,i10);
    env = env.plus(y,i15);
    Mode setMode = set.chooseMode(env);
    Assert.assertTrue(setMode != null);
    Mode memMode = mem.chooseMode(setMode.getEnvir());
    Assert.assertTrue(memMode != null);
    // evaluate the set first.
    set.setMode(setMode);
    set.startEvaluation();
    Assert.assertTrue(set.nextEvaluation());
    // now start the membership evaluation.
    mem.setMode(memMode);
    mem.startEvaluation();
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i10, memMode.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i11, memMode.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i12, memMode.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i13, memMode.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i14, memMode.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i15, memMode.getEnvir().lookup(w));
    Assert.assertFalse(mem.nextEvaluation());
    mem.startEvaluation();
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i10, memMode.getEnvir().lookup(w));
  }
}




