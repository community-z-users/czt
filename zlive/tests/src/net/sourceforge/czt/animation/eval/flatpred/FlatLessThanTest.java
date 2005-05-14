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
public class FlatLessThanTest
  extends TestCase
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private final double ACCURACY = 0.01;
  private List emptyList = new ArrayList();
  private Envir empty = new Envir();
  private BigInteger a = new BigInteger("10");
  private BigInteger b = new BigInteger("20");
  private BigInteger c = new BigInteger("21");
  private BigInteger d = new BigInteger("22");
  private BigInteger e = new BigInteger("23");
  private BigInteger f = new BigInteger("24");
  private BigInteger g = new BigInteger("25");
  private BigInteger h = new BigInteger("26");
  private BigInteger i = new BigInteger("27");
  private RefName x = factory_.createRefName("x",emptyList,null);
  private RefName y = factory_.createRefName("y",emptyList,null);
  private Expr i10 = factory_.createNumExpr(a);
  private Expr i20 = factory_.createNumExpr(b);
  private Expr i21 = factory_.createNumExpr(c);
  private Expr i22 = factory_.createNumExpr(d);
  private Expr i23 = factory_.createNumExpr(e);
  private Expr i24 = factory_.createNumExpr(f);
  private Expr i25 = factory_.createNumExpr(g);
  private Expr i26 = factory_.createNumExpr(h);
  private Expr i27 = factory_.createNumExpr(i);
  private FlatPred pred = new FlatLessThan(x,y);

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
    Assert.assertEquals(2, m.getNumArgs());
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(0.5, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  10 < 20
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(y));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which fails:  10 < 10
    pred.getMode().getEnvir().setValue(y, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIO()
  {
    Envir envX = empty.add(x,i20);
    Mode m = pred.chooseMode(envX);
    Assert.assertTrue(m != null);
    Assert.assertEquals(2, m.getNumArgs());
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(false, m.isInput(1));
    Assert.assertTrue(m.getEnvir().isDefined(y));
    Assert.assertEquals(Double.MAX_VALUE, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
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
    Assert.assertEquals(2, m.getNumArgs());
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(Double.MAX_VALUE, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
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




