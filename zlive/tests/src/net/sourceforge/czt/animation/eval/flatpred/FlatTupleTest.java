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
public class FlatTupleTest
  extends TestCase
{
  private Factory factory_ = new Factory(new ZFactoryImpl());

  private final double ACCURACY = 0.01;
  private List emptyList = new ArrayList();
  private Envir empty = new Envir();
  private BigInteger big10 = new BigInteger("10");
  private BigInteger big11 = new BigInteger("11");
  private BigInteger big12 = new BigInteger("12");
  private BigInteger big13 = new BigInteger("13");
  private BigInteger big14 = new BigInteger("14");
  private ZRefName w = factory_.createZRefName("w",emptyList,null);
  private ZRefName z = factory_.createZRefName("z",emptyList,null);
  private ZRefName l = factory_.createZRefName("l",emptyList,null);
  private ZRefName m = factory_.createZRefName("m",emptyList,null);
  private ZRefName n = factory_.createZRefName("n",emptyList,null);
  private ZRefName o = factory_.createZRefName("o",emptyList,null);
  private ZRefName p = factory_.createZRefName("p",emptyList,null);
  private ZRefName a = factory_.createZRefName("a",emptyList,null);
  private ZRefName b = factory_.createZRefName("b",emptyList,null);
  private ZRefName c = factory_.createZRefName("c",emptyList,null);
  private ZRefName d = factory_.createZRefName("d",emptyList,null);
  private ZRefName e = factory_.createZRefName("e",emptyList,null);
  private Expr i10 = factory_.createNumExpr(big10);
  private Expr i11 = factory_.createNumExpr(big11);
  private Expr i12 = factory_.createNumExpr(big12);
  private Expr i13 = factory_.createNumExpr(big13);
  private Expr i14 = factory_.createNumExpr(big14);
  private ArrayList tupleList = new ArrayList();
  private FlatPred pred;

  public FlatTupleTest()
  {
    tupleList.add(l);
    tupleList.add(m);
    tupleList.add(n);
    tupleList.add(o);
    tupleList.add(p);
    pred = new FlatTuple(tupleList,z);
  }

  public void testEmpty()
  {
    Assert.assertNull("should not return a mode", pred.chooseMode(empty));
  }

  public void testPartialI0()
  {
    Envir envL = empty.add(l,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envL));
  }

  public void testIO()
  {
    //Adding all the elements in the tuple to the environment
    Envir envLMNOP = empty.add(l,i10).add(m,i11).add(n,i12).add(o,i13).add(p,i14);
    Mode mode = null;
    Assert.assertFalse(envLMNOP.isDefined(z));
    mode = pred.chooseMode(envLMNOP);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(6, mode.getNumArgs());
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
    List exprList = tupleExpr.getExpr();
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
    Envir envABCDE = empty.add(a,i10).add(b,i11).add(c,i12).add(d,i13).add(e,i14);
    Mode mode = null;
    ArrayList tempList = new ArrayList();
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
    Envir envABCDEZ = envABCDE.add(z,tempMode.getEnvir().lookup(w));
    mode = pred.chooseMode(envABCDEZ);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(l));
    Assert.assertTrue(mode.getEnvir().isDefined(m));
    Assert.assertTrue(mode.getEnvir().isDefined(n));
    Assert.assertTrue(mode.getEnvir().isDefined(o));
    Assert.assertTrue(mode.getEnvir().isDefined(p));
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(6, mode.getNumArgs());
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
    Envir envABCDE = empty.add(a,i10).add(b,i11).add(c,i12).add(d,i13).add(e,i14);
    Mode mode = null;
    ArrayList tempList = new ArrayList();
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
    Envir envABCDEZ = envABCDE.add(z,tempMode.getEnvir().lookup(w));
    //Adding the ZRefName m to the envir, which is compliant with its corresponding value in the tuple
    Envir envABCDEZM = envABCDEZ.add(m,i11);
    mode = pred.chooseMode(envABCDEZM);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(l));
    Assert.assertTrue(mode.getEnvir().isDefined(m));
    Assert.assertTrue(mode.getEnvir().isDefined(n));
    Assert.assertTrue(mode.getEnvir().isDefined(o));
    Assert.assertTrue(mode.getEnvir().isDefined(p));
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(6, mode.getNumArgs());
    Assert.assertEquals(false, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertEquals(false, mode.isInput(2));
    Assert.assertEquals(false, mode.isInput(3));
    Assert.assertEquals(false, mode.isInput(4));
    Assert.assertEquals(true, mode.isInput(5));
    Assert.assertEquals(0.5, mode.getSolutions(), ACCURACY);
    pred.setMode(mode);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, mode.getEnvir().lookup(l));
    Assert.assertEquals("result value", i11, mode.getEnvir().lookup(m));
    Assert.assertEquals("result value", i12, mode.getEnvir().lookup(n));
    Assert.assertEquals("result value", i13, mode.getEnvir().lookup(o));
    Assert.assertEquals("result value", i14, mode.getEnvir().lookup(p));
    Assert.assertFalse(pred.nextEvaluation());
    
    //Adding the ZRefName m to the envir, which is NOT compliant with its corresponding value in the tuple
    Envir envABCDEZMN = envABCDEZM.add(n,i13);
    mode = null;
    mode = pred.chooseMode(envABCDEZMN);
    Assert.assertTrue(mode != null);
    Assert.assertTrue(mode.getEnvir().isDefined(l));
    Assert.assertTrue(mode.getEnvir().isDefined(m));
    Assert.assertTrue(mode.getEnvir().isDefined(n));
    Assert.assertTrue(mode.getEnvir().isDefined(o));
    Assert.assertTrue(mode.getEnvir().isDefined(p));
    Assert.assertTrue(mode.getEnvir().isDefined(z));
    Assert.assertEquals(6, mode.getNumArgs());
    Assert.assertEquals(false, mode.isInput(0));
    Assert.assertEquals(true, mode.isInput(1));
    Assert.assertEquals(true, mode.isInput(2));
    Assert.assertEquals(false, mode.isInput(3));
    Assert.assertEquals(false, mode.isInput(4));
    Assert.assertEquals(true, mode.isInput(5));
    Assert.assertEquals(0.5, mode.getSolutions(), ACCURACY);
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




