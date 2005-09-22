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
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatLessThanEqualsTest
  extends ZTestCase
{
  private FlatPred pred = new FlatLessThanEquals(x,y);

  public void testEmpty()
  {
    Assert.assertNull("should not return a mode", pred.chooseMode(empty));
  }

  public void testII()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i20);
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(0.5, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  10 <= 20
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(y));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  10 <= 10
    pred.getMode().getEnvir().setValue(y, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which fails:  10 <= 5
    pred.getMode().getEnvir().setValue(y, i5);  // updates the environment
    pred.startEvaluation();
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIO()
  {
    Envir envX = empty.add(x,i20);
    Mode m = pred.chooseMode(envX);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(false, m.isInput(1));
    Assert.assertTrue(m.getEnvir().isDefined(y));
    Assert.assertEquals(Double.MAX_VALUE, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(y));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i21, m.getEnvir().lookup(y));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i22, m.getEnvir().lookup(y));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i23, m.getEnvir().lookup(y));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i24, m.getEnvir().lookup(y));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i25, m.getEnvir().lookup(y));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i26, m.getEnvir().lookup(y));
  }

  public void testOI()
  {
    Envir envY = empty.add(y,i27);
    Mode m = pred.chooseMode(envY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(Double.MAX_VALUE, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i27, m.getEnvir().lookup(x));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i26, m.getEnvir().lookup(x));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i25, m.getEnvir().lookup(x));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i24, m.getEnvir().lookup(x));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i23, m.getEnvir().lookup(x));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i22, m.getEnvir().lookup(x));
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i21, m.getEnvir().lookup(x));
  }
}




