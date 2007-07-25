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
public class FlatDivTest
  extends ZTestCase
{
  private FlatPred pred = new FlatDiv(x,y,z);

  public void testToString()
  {
    assertEquals("z = x div y", pred.toString());
  }

  public void testEmpty()
  {
    Assert.assertNull("should not return a mode", pred.chooseMode(empty));
  }

  public void testIOO()
  {
    Envir envX = empty.plus(x,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envX));
  }

  public void testOIO()
  {
    Envir envY = empty.plus(y,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envY));
  }

  public void testOOI()
  {
    Envir envZ = empty.plus(z,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envZ));
  }

  public void testIII()
  {
    Envir envX = empty.plus(x,i10);
    Envir envXY = envX.plus(y,in3);
    Envir envXYZ = envXY.plus(z,in4);
    Mode m = pred.chooseMode(envXYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  div(10,-3) = -4
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", in4, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  div(10,3) = 3
    pred.getMode().getEnvir().setValue(y, i3);  // updates the environment
    pred.getMode().getEnvir().setValue(z, i3);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i3, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIIO()
  {
    Envir envX = empty.plus(x,in6);
    Envir envXY = envX.plus(y,in5);
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  div(-6,-5) = 1
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i1, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  div(-5,3) = -2
    pred.getMode().getEnvir().setValue(x, in5);  // updates the environment
    pred.getMode().getEnvir().setValue(y, i3);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", in2, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIOI()
  {
    Envir envX = empty.plus(x,in5);
    Envir envXZ = envX.plus(z,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envXZ));
  }

  public void testOII()
  {
    Envir envY = empty.plus(y,in6);
    Envir envYZ = envY.plus(z,in3);
    Assert.assertNull("should not return a mode", pred.chooseMode(envYZ));
  }
}




