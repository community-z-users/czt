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
public class FlatDiscreteSetTest
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
  private RefName x = factory_.createRefName("x",emptyList,null);
  private RefName y = factory_.createRefName("y",emptyList,null);
  private RefName z = factory_.createRefName("z",emptyList,null);
  private RefName w = factory_.createRefName("w",emptyList,null);
  private RefName l = factory_.createRefName("l",emptyList,null);
  private RefName m = factory_.createRefName("m",emptyList,null);
  private RefName n = factory_.createRefName("n",emptyList,null);
  private RefName o = factory_.createRefName("o",emptyList,null);
  private RefName p = factory_.createRefName("p",emptyList,null);
  private RefName q = factory_.createRefName("q",emptyList,null);
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
  private ArrayList argsList = new ArrayList();
  protected EvalSet set;
  
  public FlatDiscreteSetTest()
  {
    argsList.add(l);
    argsList.add(m);
    argsList.add(n);
    argsList.add(o);
    argsList.add(p);
    argsList.add(q);
    set = new FlatDiscreteSet(argsList,z); 
  }
  
  public void testEmpty()
  {
    Mode m = ((FlatPred)set).chooseMode(empty);
    Assert.assertNull(m);
  }
  
  public void testIOO()
  {
    Envir envL = empty.add(l,i10);
    Mode m = ((FlatPred)set).chooseMode(envL);
    Assert.assertNull(m);
  }
  
  public void testOIO()
  {
    Envir envM = empty.add(m,i10);
    Mode m = ((FlatPred)set).chooseMode(envM);
    Assert.assertNull(m);
  }
  
  /*public void testEmptySet()
  {
    /*Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i30);
    Mode m = ((FlatPred)emptySet).chooseMode(envXY);
    Assert.assertTrue(m != null);
    ((FlatPred)emptySet).setMode(m);
    ((FlatPred)emptySet).startEvaluation();
    Assert.assertTrue(((FlatPred)emptySet).nextEvaluation());
    EvalSet tempSet = (EvalSet)m.getEnvir().lookup(z);
    Assert.assertTrue(tempSet == emptySet);
    Assert.assertEquals(0.0,emptySet.estSize(),ACCURACY);
    Iterator it = tempSet.members();
    Assert.assertTrue(it != null);
    Assert.assertFalse(it.hasNext());
    Assert.assertFalse(emptySet.isMember(i10));
    Assert.assertFalse(emptySet.isMember(i30));
    Assert.assertFalse(((FlatPred)emptySet).nextEvaluation());
  }*/
  
  public void testII0()
  {
    Envir envLMNOPQ = empty.add(l,i10);
    envLMNOPQ = envLMNOPQ.add(m,i11);
    envLMNOPQ = envLMNOPQ.add(n,i12);
    envLMNOPQ = envLMNOPQ.add(o,i13);
    envLMNOPQ = envLMNOPQ.add(p,i14);
    envLMNOPQ = envLMNOPQ.add(q,i15);
    Mode mode = ((FlatPred)set).chooseMode(envLMNOPQ);
    Assert.assertTrue(mode != null);
    ((FlatPred)set).setMode(mode);
    ((FlatPred)set).startEvaluation();
    Assert.assertTrue(((FlatPred)set).nextEvaluation());
    Assert.assertTrue(mode.getEnvir().lookup(z) != null);
    //Checking the estSize() method
    Assert.assertEquals(6.0, set.estSize(), ACCURACY);
    //Checking the freeVars() method
    ArrayList temp = (ArrayList)set.freeVars();
    Assert.assertTrue(temp.size() == 6);
    Assert.assertTrue(temp.contains(l));
    Assert.assertTrue(temp.contains(m));
    Assert.assertTrue(temp.contains(n));
    Assert.assertTrue(temp.contains(o));
    Assert.assertTrue(temp.contains(p));
    Assert.assertTrue(temp.contains(q));
    //Checking the isMember() method
    Assert.assertTrue(set.isMember(i10));
    Assert.assertTrue(set.isMember(i11));
    Assert.assertTrue(set.isMember(i15));
    Assert.assertFalse(set.isMember(i20));
    Assert.assertFalse(set.isMember(i40));
    //Checking the members() method
    Set allElements = new HashSet();
    Iterator it = set.members();
    //All the elements of in the set are added to a HashSet
    while (it.hasNext())
      allElements.add(it.next());
    //Another HashSet named comparisonSet is being created which contains
    //the same elements as the allElements should contain logically
    Set comparisonSet = new HashSet();
    comparisonSet.add(i10);
    comparisonSet.add(i13);
    comparisonSet.add(i12);
    comparisonSet.add(i11);
    comparisonSet.add(i14);
    comparisonSet.add(i15);
    //This compares the two HashSets, and checks if they are equal
    Assert.assertTrue(allElements.equals(comparisonSet));
    Assert.assertFalse(((FlatPred)set).nextEvaluation());
  }
  
  public void testIII()
  {
    Envir envLMNOPQ = empty.add(l,i10);
    envLMNOPQ = envLMNOPQ.add(m,i11);
    envLMNOPQ = envLMNOPQ.add(n,i12);
    envLMNOPQ = envLMNOPQ.add(o,i13);
    envLMNOPQ = envLMNOPQ.add(p,i14);
    envLMNOPQ = envLMNOPQ.add(q,i15);
    ArrayList tempList = new ArrayList();
    tempList.add(l);
    tempList.add(m);
    tempList.add(n);
    tempList.add(o);
    tempList.add(p);
    tempList.add(q);
    EvalSet tempDiscreteSet = new FlatDiscreteSet(tempList, w);
    Mode tempMode = ((FlatPred)tempDiscreteSet).chooseMode(envLMNOPQ);
    ((FlatPred)tempDiscreteSet).setMode(tempMode);
    ((FlatPred)tempDiscreteSet).startEvaluation();
    ((FlatPred)tempDiscreteSet).nextEvaluation();
    Envir envLMNOPQZ = envLMNOPQ.add(z,(EvalSet)(((FlatPred)tempDiscreteSet).getMode().getEnvir().lookup(w)));
    Mode mode = ((FlatPred)set).chooseMode(envLMNOPQZ);
    Assert.assertTrue(mode != null);
    ((FlatPred)set).setMode(mode);
    ((FlatPred)set).startEvaluation();
    Assert.assertTrue(((FlatPred)set).nextEvaluation());
    Assert.assertFalse(((FlatPred)set).nextEvaluation());
  }
}




