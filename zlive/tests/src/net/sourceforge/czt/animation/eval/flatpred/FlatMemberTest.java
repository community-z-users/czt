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
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;


/**
 * A (JUnit) test class for testing the Animator
 * TODO split this into separate tests for each kind of EvalSet.
 *
 * @author Mark Utting
 */
public class FlatMemberTest
  extends TestCase
{
  private Factory factory_ = new Factory();

  private final double ACCURACY = 0.01;
  private List emptyList = new ArrayList();
  private Envir empty = new Envir();
  private BigInteger a = new BigInteger("10");
  private BigInteger b = new BigInteger("20");
  private BigInteger c = new BigInteger("30");
  private BigInteger d = new BigInteger("40");
  private BigInteger e = new BigInteger("5");
  private BigInteger f = new BigInteger("11");
  private BigInteger g = new BigInteger("12");
  private BigInteger h = new BigInteger("13");
  private BigInteger i = new BigInteger("14");
  private BigInteger j = new BigInteger("15");
  private BigInteger k = new BigInteger("16");
  private RefName x = factory_.createRefName("x",emptyList,null);
  private RefName y = factory_.createRefName("y",emptyList,null);
  private RefName z = factory_.createRefName("z",emptyList,null);
  private RefName w = factory_.createRefName("w",emptyList,null);
  private Expr i10 = factory_.createNumExpr(a);
  private Expr i20 = factory_.createNumExpr(b);
  private Expr i30 = factory_.createNumExpr(c);
  private Expr i40 = factory_.createNumExpr(d);
  private Expr i5 = factory_.createNumExpr(e);
  private Expr i11 = factory_.createNumExpr(f);
  private Expr i12 = factory_.createNumExpr(g);
  private Expr i13 = factory_.createNumExpr(h);
  private Expr i14 = factory_.createNumExpr(i);
  private Expr i15 = factory_.createNumExpr(j);
  private FlatRangeSet set = new FlatRangeSet(x,y,z);
  private FlatMember mem = new FlatMember(z,w);

  public void testEmpty()
  {
    Mode m = mem.chooseMode(empty);
    Assert.assertNull(m);
  }

  public void testOI()
  {
    Envir envW = empty.add(w,i20);
    Mode m = mem.chooseMode(envW);
    Assert.assertNull(m);
  }

  /** Disable these temporarily, until FlatRangeSet is fixed.
  public void testII()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i40);
    Envir envXYW = envXY.add(w,i20);
    Mode m = set.chooseMode(envXYW);
    Assert.assertTrue(m != null);
    m = mem.chooseMode(m.getEnvir());
    Assert.assertTrue(m != null);
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(w));
    mem.setMode(m);
    // Start an Evaluation which succeeds. 20 (memberOf) 10..40
    mem.startEvaluation();
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertFalse(mem.nextEvaluation());
    //Start an Evaluation which fails. 5 (memberOf) 10..40
    m.getEnvir().setValue(w,i5);
    mem.startEvaluation();
    Assert.assertFalse(mem.nextEvaluation());
  }

  public void testIO()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i15);
    Mode m = set.chooseMode(envXY);
    Assert.assertTrue(m != null);
    m = mem.chooseMode(m.getEnvir());
    Assert.assertTrue(m != null);
    mem.setMode(m);
    mem.startEvaluation();
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i11, m.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i12, m.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i13, m.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i14, m.getEnvir().lookup(w));
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i15, m.getEnvir().lookup(w));
    Assert.assertFalse(mem.nextEvaluation());
    mem.startEvaluation();
    Assert.assertTrue(mem.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(w));
  }
  
  public void testSpecialCases()
  {
    Envir envZ = empty.add(z,new FlatRangeSet(x,y));
    Mode m = mem.chooseMode(envZ);
    Assert.assertNull(m);
    //Assert.assertEquals(1000000.0, m.getSolutions(), ACCURACY);
    Envir envZW = envZ.add(w,i20);
    m = null;
    m = mem.chooseMode(envZW);
    Assert.assertNull(m);
    //Assert.assertEquals(0.5, m.getSolutions(), ACCURACY);
  }
  */
}




