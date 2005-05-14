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
public class FlatConstTest
  extends TestCase
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private final double ACCURACY = 0.01;
  private List emptyList = new ArrayList();
  private Envir empty = new Envir();
  private BigInteger a = new BigInteger("10");
  private BigInteger b = new BigInteger("20");
  private RefName x = factory_.createRefName("x",emptyList,null);
  private Expr i10 = factory_.createNumExpr(a);
  private Expr i20 = factory_.createNumExpr(b);
  private FlatPred pred = new FlatConst(x,i10);

  public void testEmpty()
  {
    Assert.assertTrue(pred.chooseMode(empty) != null);
  }

  public void testI()
  {
    Envir envX = empty.add(x,i10);
    Mode m = pred.chooseMode(envX);
    Assert.assertTrue(m != null);
    Assert.assertEquals(1, m.getNumArgs());
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(0.5, m.getSolutions(), ACCURACY);
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
    Assert.assertEquals(1, m.getNumArgs());
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(1.0, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
  }
}




