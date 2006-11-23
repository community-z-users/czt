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

import java.util.ArrayList;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the Animator
 * @author Mark Utting
 */
public class FlatCardTest
  extends ZTestCase
{
  private ZName l = factory_.createZName("l");
  private ZName m = factory_.createZName("m");
  private ZName n = factory_.createZName("n");
  private ZName o = factory_.createZName("o");
  private ZName p = factory_.createZName("p");
  private ZName q = factory_.createZName("q");

  private ZName s = factory_.createZName("s");

  private ZName w = factory_.createZName("w");
  
  protected FlatPred pred;

  public void setUp()
  {
    pred = new FlatCard(z,s);
    pred.inferBounds(new Bounds());
  }

  public void testEmpty()
  {
    Mode m = pred.chooseMode(empty);
    Assert.assertNull(m);
  }

  public void testOI()
  {
    Envir envS = empty.plus(s,i6);
    Mode m = pred.chooseMode(envS);
    Assert.assertNull(m);
  }

  public void testRangeSetIO()
  {
    Envir envX = empty.plus(x,i10);
    Envir envXY = envX.plus(y,i15);
    EvalSet tempRangeSet = new FlatRangeSet(x,y,w);
    Mode tempMode = ((FlatPred)tempRangeSet).chooseMode(envXY);
    ((FlatPred)tempRangeSet).setMode(tempMode);
    ((FlatPred)tempRangeSet).startEvaluation();
    ((FlatPred)tempRangeSet).nextEvaluation();
    Envir envXYZ = envXY.plus(z,(EvalSet)(((FlatPred)tempRangeSet).getMode().getEnvir().lookup(w)));
    Mode mode = pred.chooseMode(envXYZ);
    Assert.assertTrue(mode != null);
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
    Envir envLMNOPQ = empty.plus(l,i10);
    envLMNOPQ = envLMNOPQ.plus(m,i11);
    envLMNOPQ = envLMNOPQ.plus(n,i12);
    envLMNOPQ = envLMNOPQ.plus(o,i13);
    envLMNOPQ = envLMNOPQ.plus(p,i14);
    envLMNOPQ = envLMNOPQ.plus(q,i15);
    ArrayList<ZName> tempArgsList = new ArrayList<ZName>();
    tempArgsList.add(l);
    tempArgsList.add(m);
    tempArgsList.add(n);
    tempArgsList.add(o);
    tempArgsList.add(p);
    tempArgsList.add(q);
    EvalSet tempDiscreteSet = new FlatDiscreteSet(tempArgsList,w);
    ((FlatPred)tempDiscreteSet).inferBounds(new Bounds()); // empty bounds
    Mode tempMode = ((FlatPred)tempDiscreteSet).chooseMode(envLMNOPQ);
    Assert.assertTrue(tempMode != null);
    ((FlatPred)tempDiscreteSet).setMode(tempMode);
    ((FlatPred)tempDiscreteSet).startEvaluation();
    ((FlatPred)tempDiscreteSet).nextEvaluation();
    Envir envLMNOPQZ = envLMNOPQ.plus(z,(EvalSet)(((FlatPred)tempDiscreteSet).getMode().getEnvir().lookup(w)));
    Mode mode = pred.chooseMode(envLMNOPQZ);
    Assert.assertTrue(mode != null);
    Assert.assertEquals(true, mode.isInput(0));
    Assert.assertEquals(false, mode.isInput(1));
    Assert.assertTrue(mode.getEnvir().isDefined(s));
    Assert.assertEquals(1.0, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertTrue(mode == pred.getMode());
    Assert.assertEquals("result value", i6, mode.getEnvir().lookup(s));
    Assert.assertFalse(pred.nextEvaluation());
    mode.getEnvir().setValue(q,i11);
    ((FlatPred)tempDiscreteSet).startEvaluation();
    ((FlatPred)tempDiscreteSet).nextEvaluation();
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i5, mode.getEnvir().lookup(s));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testRangeSetII()
  {
    // create and evaluate: w = x..y
    Envir envX = empty.plus(x,i10);
    Envir envXY = envX.plus(y,i15);
    EvalSet tempRangeSet = new FlatRangeSet(x,y,w);
    ((FlatPred)tempRangeSet).inferBounds(new Bounds()); // no bounds
    Mode tempMode = ((FlatPred)tempRangeSet).chooseMode(envXY);
    ((FlatPred)tempRangeSet).setMode(tempMode);
    ((FlatPred)tempRangeSet).startEvaluation();
    ((FlatPred)tempRangeSet).nextEvaluation();
    Envir envXYZ = envXY.plus(z,(EvalSet)(((FlatPred)tempRangeSet).getMode().getEnvir().lookup(w)));
    
    // now check #w = 6
    Envir envXYZS = envXYZ.plus(s,i6);
    Mode mode = pred.chooseMode(envXYZS);
    Assert.assertTrue(mode != null);
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
    // create and evaluate: w = {l,m,n,o,p,q}
    Envir envLMNOPQ = empty.plus(l,i10);
    envLMNOPQ = envLMNOPQ.plus(m,i11);
    envLMNOPQ = envLMNOPQ.plus(n,i12);
    envLMNOPQ = envLMNOPQ.plus(o,i13);
    envLMNOPQ = envLMNOPQ.plus(p,i14);
    envLMNOPQ = envLMNOPQ.plus(q,i15);
    ArrayList<ZName> tempArgsList = new ArrayList<ZName>();
    tempArgsList.add(l);
    tempArgsList.add(m);
    tempArgsList.add(n);
    tempArgsList.add(o);
    tempArgsList.add(p);
    tempArgsList.add(q);
    EvalSet tempDiscreteSet = new FlatDiscreteSet(tempArgsList,w);
    ((FlatPred)tempDiscreteSet).inferBounds(new Bounds()); // empty bounds
    Mode tempMode = ((FlatPred)tempDiscreteSet).chooseMode(envLMNOPQ);
    Assert.assertTrue(tempMode != null);
    ((FlatPred)tempDiscreteSet).setMode(tempMode);
    ((FlatPred)tempDiscreteSet).startEvaluation();
    ((FlatPred)tempDiscreteSet).nextEvaluation();
    Envir envLMNOPQZ = envLMNOPQ.plus(z,(EvalSet)(((FlatPred)tempDiscreteSet).getMode().getEnvir().lookup(w)));
    
    // now check that #w = 6.
    Envir envLMNOPQZS = envLMNOPQZ.plus(s,i6);
    Mode mode = pred.chooseMode(envLMNOPQZS);
    Assert.assertTrue(mode != null);
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




