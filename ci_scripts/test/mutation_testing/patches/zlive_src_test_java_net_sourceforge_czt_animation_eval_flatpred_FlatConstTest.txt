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


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatConstTest
  extends ZTestCase
{
  private FlatPred pred = new FlatConst(x,i10);

  public void testToString()
  {
    assertEquals("x == 10", pred.toString());
  }

  public void testEmpty()
  {
    Assert.assertTrue(pred.chooseMode(empty) != null);
  }

  public void testI()
  {
    Envir envX = empty.plus(x,i10);
    Mode m = pred.chooseMode(envX);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  x (=10) = 10
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which fails:  x (=20) = 10
    pred.getMode().getEnvir().setValue(x, i20);  // updates the environment
    pred.startEvaluation();
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testO()
  {
    Mode m = pred.chooseMode(empty);
    Assert.assertTrue(m != null);
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
  }
}




