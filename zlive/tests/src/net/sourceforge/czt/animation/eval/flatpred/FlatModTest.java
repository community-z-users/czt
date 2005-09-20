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

import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.math.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatModTest
  extends ZTestCase
{
  private FlatPred pred = new FlatMod(x,y,z);

  public void testEmpty()
  {
    Assert.assertNull("should not return a mode", pred.chooseMode(empty));
  }

  public void testIOO()
  {
    Envir envX = empty.add(x,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envX));
  }

  public void testOIO()
  {
    Envir envY = empty.add(y,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envY));
  }

  public void testOOI()
  {
    Envir envZ = empty.add(z,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envZ));
  }

  public void testIII()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,in3);
    Envir envXYZ = envXY.add(z,in2);
    Mode m = pred.chooseMode(envXYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(3, m.getNumArgs());
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertEquals(0.5, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  mod(10,-3) = -2
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", in2, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  mod(10,3) = 1
    pred.getMode().getEnvir().setValue(y, i3);  // updates the environment
    pred.getMode().getEnvir().setValue(z, i1);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i1, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIIO()
  {
    Envir envX = empty.add(x,in6);
    Envir envXY = envX.add(y,in5);
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(3, m.getNumArgs());
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(1.0, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  mod(-6,-5) = -1
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", in1, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  mod(-5,3) = 1
    pred.getMode().getEnvir().setValue(x, in5);  // updates the environment
    pred.getMode().getEnvir().setValue(y, i3);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i1, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIOI()
  {
    Envir envX = empty.add(x,in5);
    Envir envXZ = envX.add(z,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envXZ));
  }

  public void testOII()
  {
    Envir envY = empty.add(y,in6);
    Envir envYZ = envY.add(z,in3);
    Assert.assertNull("should not return a mode", pred.chooseMode(envY));
  }
}




