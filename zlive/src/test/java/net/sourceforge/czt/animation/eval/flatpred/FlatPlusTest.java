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

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.NumExpr;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatPlusTest
  extends ZTestCase
{
  private FlatPred pred = new FlatPlus(x,y,z);

  public void testToString()
  {
    assertEquals("z = x + y", pred.toString());
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
    Envir envXY = envX.plus(y,i20);
    Envir envXYZ = envXY.plus(z,i30);
    Mode m = pred.chooseMode(envXYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  10+20=30
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i30, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which fails:  10+20=10
    pred.getMode().getEnvir().setValue(z, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIIO()
  {
    Envir envX = empty.plus(x,i10);
    Envir envXY = envX.plus(y,i20);
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i30, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  /** Similar to testIIO, but with big integer values */
  public void testIIOBigInteger()
  {
    BigInteger twoB = BigInteger.valueOf(2000000000);
    Envir envX = empty.plus(x,factory_.createNumExpr(twoB));
    Envir envXY = envX.plus(y,factory_.createNumExpr(twoB));
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    NumExpr fourB = factory_.createNumExpr(factory_.createZNumeral(
        BigInteger.valueOf(1000000000).multiply(BigInteger.valueOf(4))));
    Assert.assertEquals("result value", fourB, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIOI()
  {
    Envir envX = empty.plus(x,i10);
    Envir envXZ = envX.plus(z,i30);
    Mode m = pred.chooseMode(envXZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(false, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(y));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(y));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testOII()
  {
    Envir envY = empty.plus(y,i20);
    Envir envYZ = envY.plus(z,i30);
    Mode m = pred.chooseMode(envYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  10+20=30
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  20+10=30
    pred.getMode().getEnvir().setValue(z, i30);  // updates the environment
    pred.getMode().getEnvir().setValue(y, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
  }
}




