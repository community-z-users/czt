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
 * @author Mark Utting
 */
public class FlatCardTest
  extends TestCase
{
  private Factory factory_ = new Factory();

  private final double ACCURACY = 0.01;
  private List emptyList = new ArrayList();
  private Envir empty = new Envir();
  private BigInteger a = new BigInteger("10");
  private BigInteger f = new BigInteger("11");
  private BigInteger g = new BigInteger("12");
  private BigInteger h = new BigInteger("13");
  private BigInteger i = new BigInteger("14");
  private BigInteger j = new BigInteger("15");
  private BigInteger k = new BigInteger("6");
  private RefName x = factory_.createRefName("x",emptyList,null);
  private RefName y = factory_.createRefName("y",emptyList,null);
  private RefName z = factory_.createRefName("z",emptyList,null);
  private RefName w = factory_.createRefName("w",emptyList,null);
  private RefName s = factory_.createRefName("s",emptyList,null);
  private RefName l = factory_.createRefName("l",emptyList,null);
  private RefName m = factory_.createRefName("m",emptyList,null);
  private RefName n = factory_.createRefName("n",emptyList,null);
  private RefName o = factory_.createRefName("o",emptyList,null);
  private RefName p = factory_.createRefName("p",emptyList,null);
  private RefName q = factory_.createRefName("q",emptyList,null);
  private Expr i10 = factory_.createNumExpr(a);
  private Expr i11 = factory_.createNumExpr(f);
  private Expr i12 = factory_.createNumExpr(g);
  private Expr i13 = factory_.createNumExpr(h);
  private Expr i14 = factory_.createNumExpr(i);
  private Expr i15 = factory_.createNumExpr(j);
  private Expr i6 = factory_.createNumExpr(k);
  protected FlatPred pred = new FlatCard(z,s);
  
  public void testEmpty()
  {
    Mode m = pred.chooseMode(empty);
    Assert.assertNull(m);
  }
  
  public void testOI()
  {
    Envir envS = empty.add(s,i6);
    Mode m = pred.chooseMode(envS);
    Assert.assertNull(m);
  }
  
  public void testRangeSetIO()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i15);
    EvalSet tempRangeSet = new FlatRangeSet(x,y,w);
    Mode tempMode = ((FlatPred)tempRangeSet).chooseMode(envXY);
    ((FlatPred)tempRangeSet).setMode(tempMode);
    ((FlatPred)tempRangeSet).startEvaluation();
    ((FlatPred)tempRangeSet).nextEvaluation();
    Envir envXYZ = envXY.add(z,(EvalSet)(((FlatPred)tempRangeSet).getMode().getEnvir().lookup(w)));
    Mode mode = pred.chooseMode(envXYZ);
    Assert.assertTrue(mode != null);
    Assert.assertEquals(2, mode.getNumArgs());
    Assert.assertEquals(true, mode.isInput(0));
    Assert.assertEquals(false, mode.isInput(1));
    Assert.assertTrue(mode.getEnvir().isDefined(s));
    Assert.assertEquals(1.0, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i6, mode.getEnvir().lookup(s));
    Assert.assertFalse(pred.nextEvaluation());
  }
  
  public void testDiscreteSetIO()
  {
    Envir envLMNOPQ = empty.add(l,i10);
    envLMNOPQ = envLMNOPQ.add(m,i11);
    envLMNOPQ = envLMNOPQ.add(n,i12);
    envLMNOPQ = envLMNOPQ.add(o,i13);
    envLMNOPQ = envLMNOPQ.add(p,i14);
    envLMNOPQ = envLMNOPQ.add(q,i15);
    ArrayList tempArgsList = new ArrayList();
    tempArgsList.add(l);
    tempArgsList.add(m);
    tempArgsList.add(n);
    tempArgsList.add(o);
    tempArgsList.add(p);
    tempArgsList.add(q);
    EvalSet tempDiscreteSet = new FlatDiscreteSet(tempArgsList,w);
    Mode tempMode = ((FlatPred)tempDiscreteSet).chooseMode(envLMNOPQ);
    Assert.assertTrue(tempMode != null);
    ((FlatPred)tempDiscreteSet).setMode(tempMode);
    ((FlatPred)tempDiscreteSet).startEvaluation();
    ((FlatPred)tempDiscreteSet).nextEvaluation();
    Envir envLMNOPQZ = envLMNOPQ.add(z,(EvalSet)(((FlatPred)tempDiscreteSet).getMode().getEnvir().lookup(w)));
    Mode mode = pred.chooseMode(envLMNOPQZ);
    Assert.assertTrue(mode != null);
    Assert.assertEquals(2, mode.getNumArgs());
    Assert.assertEquals(true, mode.isInput(0));
    Assert.assertEquals(false, mode.isInput(1));
    Assert.assertTrue(mode.getEnvir().isDefined(s));
    Assert.assertEquals(1.0, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i6, mode.getEnvir().lookup(s));
    Assert.assertFalse(pred.nextEvaluation());
  }
  
  public void testRangeSetII()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i15);
    EvalSet tempRangeSet = new FlatRangeSet(x,y,w);
    Mode tempMode = ((FlatPred)tempRangeSet).chooseMode(envXY);
    ((FlatPred)tempRangeSet).setMode(tempMode);
    ((FlatPred)tempRangeSet).startEvaluation();
    ((FlatPred)tempRangeSet).nextEvaluation();
    Envir envXYZ = envXY.add(z,(EvalSet)(((FlatPred)tempRangeSet).getMode().getEnvir().lookup(w)));
    Envir envXYZS = envXYZ.add(s,i6);
    Mode mode = pred.chooseMode(envXYZS);
    Assert.assertTrue(mode != null);
    Assert.assertEquals(2, mode.getNumArgs());
    Assert.assertEquals(true, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertTrue(mode.getEnvir().isDefined(s));
    Assert.assertEquals(0.5, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i6, mode.getEnvir().lookup(s));
    Assert.assertFalse(pred.nextEvaluation());
  }
  
  public void testDiscreteSetII()
  {
    Envir envLMNOPQ = empty.add(l,i10);
    envLMNOPQ = envLMNOPQ.add(m,i11);
    envLMNOPQ = envLMNOPQ.add(n,i12);
    envLMNOPQ = envLMNOPQ.add(o,i13);
    envLMNOPQ = envLMNOPQ.add(p,i14);
    envLMNOPQ = envLMNOPQ.add(q,i15);
    ArrayList tempArgsList = new ArrayList();
    tempArgsList.add(l);
    tempArgsList.add(m);
    tempArgsList.add(n);
    tempArgsList.add(o);
    tempArgsList.add(p);
    tempArgsList.add(q);
    EvalSet tempDiscreteSet = new FlatDiscreteSet(tempArgsList,w);
    Mode tempMode = ((FlatPred)tempDiscreteSet).chooseMode(envLMNOPQ);
    Assert.assertTrue(tempMode != null);
    ((FlatPred)tempDiscreteSet).setMode(tempMode);
    ((FlatPred)tempDiscreteSet).startEvaluation();
    ((FlatPred)tempDiscreteSet).nextEvaluation();
    Envir envLMNOPQZ = envLMNOPQ.add(z,(EvalSet)(((FlatPred)tempDiscreteSet).getMode().getEnvir().lookup(w)));
    Envir envLMNOPQZS = envLMNOPQZ.add(s,i6);
    Mode mode = pred.chooseMode(envLMNOPQZS);
    Assert.assertTrue(mode != null);
    Assert.assertEquals(2, mode.getNumArgs());
    Assert.assertEquals(true, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertTrue(mode.getEnvir().isDefined(s));
    Assert.assertEquals(0.5, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i6, mode.getEnvir().lookup(s));
    Assert.assertFalse(pred.nextEvaluation());
  }

}




