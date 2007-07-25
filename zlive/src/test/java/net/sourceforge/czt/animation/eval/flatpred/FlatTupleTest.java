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
import java.util.List;
import java.util.Map;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatTupleTest
  extends ZTestCase
{
  private ZName w = factory_.createZName("w");

  private ZName l = factory_.createZName("l");
  private ZName m = factory_.createZName("m");
  private ZName n = factory_.createZName("n");
  private ZName o = factory_.createZName("o");
  private ZName p = factory_.createZName("p");

  private ZName a = factory_.createZName("a");
  private ZName b = factory_.createZName("b");
  private ZName c = factory_.createZName("c");
  private ZName d = factory_.createZName("d");
  private ZName e = factory_.createZName("e");

  private FlatPred pred;

  public FlatTupleTest()
  {
    ArrayList<ZName> tupleList = new ArrayList<ZName>();
    tupleList.add(l);
    tupleList.add(m);
    tupleList.add(n);
    tupleList.add(o);
    tupleList.add(p);
    pred = new FlatTuple(tupleList,z);
  }

  public void testToString()
  {
    assertEquals("z = (l, m, n, o, p)", pred.toString());
  }

  public void testBounds()
  {
    Bounds bnds = new Bounds(null);
    pred.inferBounds(bnds);
    Map<Object, ZName> args = bnds.getStructure(z);
    assertNotNull(args);
    assertEquals(l, args.get(Integer.valueOf(1)));
    assertEquals(p, args.get(Integer.valueOf(5)));
  }

  public void testEmpty()
  {
    Assert.assertNull("should not return a mode", pred.chooseMode(empty));
  }

  public void testPartialI0()
  {
    Envir envL = empty.plus(l,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envL));
  }

  public void testIO()
  {
    //Adding all the elements in the tuple to the environment
    Envir envLMNOP = empty.plus(l,i10).plus(m,i11).plus(n,i12).plus(o,i13).plus(p,i14);
    Mode mode = null;
    Assert.assertFalse(envLMNOP.isDefined(z));
    mode = pred.chooseMode(envLMNOP);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(true, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertEquals(true, mode.isInput(2));
    Assert.assertEquals(true, mode.isInput(3));
    Assert.assertEquals(true, mode.isInput(4));
    Assert.assertEquals(false, mode.isInput(5));
    Assert.assertEquals(1.0, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertTrue(mode.getEnvir().lookup(z) instanceof TupleExpr);
    TupleExpr tupleExpr = (TupleExpr)mode.getEnvir().lookup(z);
    List<Expr> exprList = tupleExpr.getZExprList();
    for(int i=0;i<exprList.size();i++)
      Assert.assertTrue(exprList.get(i) instanceof NumExpr);
    Assert.assertTrue(exprList.get(0).equals(i10));
    Assert.assertTrue(exprList.get(1).equals(i11));
    Assert.assertTrue(exprList.get(2).equals(i12));
    Assert.assertTrue(exprList.get(3).equals(i13));
    Assert.assertTrue(exprList.get(4).equals(i14));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testOI()
  {
    Envir envABCDE = empty.plus(a,i10).plus(b,i11).plus(c,i12).plus(d,i13).plus(e,i14);
    Mode mode = null;
    ArrayList<ZName> tempList = new ArrayList<ZName>();
    tempList.add(a);
    tempList.add(b);
    tempList.add(c);
    tempList.add(d);
    tempList.add(e);
    //creating a temporary tuple to add to the environment
    FlatPred tempTuple = new FlatTuple(tempList,w);
    Mode tempMode = tempTuple.chooseMode(envABCDE);
    tempTuple.setMode(tempMode);
    tempTuple.startEvaluation();
    tempTuple.nextEvaluation();
    Assert.assertTrue(tempMode.getEnvir().lookup(w) instanceof TupleExpr);
    //Adding z to the Envir with its value as the temporary tuple created above
    Envir envABCDEZ = envABCDE.plus(z,tempMode.getEnvir().lookup(w));
    mode = pred.chooseMode(envABCDEZ);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(l));
    Assert.assertTrue(mode.getEnvir().isDefined(m));
    Assert.assertTrue(mode.getEnvir().isDefined(n));
    Assert.assertTrue(mode.getEnvir().isDefined(o));
    Assert.assertTrue(mode.getEnvir().isDefined(p));
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(false, mode.isInput(0));
    Assert.assertEquals(false, mode.isInput(1));
    Assert.assertEquals(false, mode.isInput(2));
    Assert.assertEquals(false, mode.isInput(3));
    Assert.assertEquals(false, mode.isInput(4));
    Assert.assertEquals(true, mode.isInput(5));
    Assert.assertEquals(1.0, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, mode.getEnvir().lookup(l));
    Assert.assertEquals("result value", i11, mode.getEnvir().lookup(m));
    Assert.assertEquals("result value", i12, mode.getEnvir().lookup(n));
    Assert.assertEquals("result value", i13, mode.getEnvir().lookup(o));
    Assert.assertEquals("result value", i14, mode.getEnvir().lookup(p));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testPartialOI()
  {
    Envir envABCDE = empty.plus(a,i10).plus(b,i11).plus(c,i12).plus(d,i13).plus(e,i14);
    Mode mode = null;
    ArrayList<ZName> tempList = new ArrayList<ZName>();
    tempList.add(a);
    tempList.add(b);
    tempList.add(c);
    tempList.add(d);
    tempList.add(e);
    //creating a temporary tuple to add to the environment
    FlatPred tempTuple = new FlatTuple(tempList,w);
    Mode tempMode = tempTuple.chooseMode(envABCDE);
    tempTuple.setMode(tempMode);
    tempTuple.startEvaluation();
    tempTuple.nextEvaluation();
    Assert.assertTrue(tempMode.getEnvir().lookup(w) instanceof TupleExpr);
    //Adding z to the Envir with its value as the temporary tuple created above
    Envir envABCDEZ = envABCDE.plus(z,tempMode.getEnvir().lookup(w));
    //Adding the ZName m to the envir, which is compliant with its corresponding value in the tuple
    Envir envABCDEZM = envABCDEZ.plus(m,i11);
    mode = pred.chooseMode(envABCDEZM);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(l));
    Assert.assertTrue(mode.getEnvir().isDefined(m));
    Assert.assertTrue(mode.getEnvir().isDefined(n));
    Assert.assertTrue(mode.getEnvir().isDefined(o));
    Assert.assertTrue(mode.getEnvir().isDefined(p));
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(false, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertEquals(false, mode.isInput(2));
    Assert.assertEquals(false, mode.isInput(3));
    Assert.assertEquals(false, mode.isInput(4));
    Assert.assertEquals(true, mode.isInput(5));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, mode.getEnvir().lookup(l));
    Assert.assertEquals("result value", i11, mode.getEnvir().lookup(m));
    Assert.assertEquals("result value", i12, mode.getEnvir().lookup(n));
    Assert.assertEquals("result value", i13, mode.getEnvir().lookup(o));
    Assert.assertEquals("result value", i14, mode.getEnvir().lookup(p));
    Assert.assertFalse(pred.nextEvaluation());

    //Adding the ZName m to the envir, which is NOT compliant with its corresponding value in the tuple
    Envir envABCDEZMN = envABCDEZM.plus(n,i13);
    mode = null;
    mode = pred.chooseMode(envABCDEZMN);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(l));
    Assert.assertTrue(mode.getEnvir().isDefined(m));
    Assert.assertTrue(mode.getEnvir().isDefined(n));
    Assert.assertTrue(mode.getEnvir().isDefined(o));
    Assert.assertTrue(mode.getEnvir().isDefined(p));
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(false, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertEquals(true, mode.isInput(2));
    Assert.assertEquals(false, mode.isInput(3));
    Assert.assertEquals(false, mode.isInput(4));
    Assert.assertEquals(true, mode.isInput(5));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    //The assertion fails because of unmatching value of n.
    //However, all the other elements are set to their respective
    //values according to the values in the tuple present in the env
    Assert.assertFalse(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, mode.getEnvir().lookup(l));
    Assert.assertEquals("result value", i11, mode.getEnvir().lookup(m));
    Assert.assertEquals("result value", i13, mode.getEnvir().lookup(n));
    Assert.assertEquals("result value", i13, mode.getEnvir().lookup(o));
    Assert.assertEquals("result value", i14, mode.getEnvir().lookup(p));
  }
}




