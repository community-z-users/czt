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
 * This tests a FlatRangeSet, mostly with the data 10..12.
 * It is also reused (via inheritance) to test other subclasses of EvalSet.
 *
 * @author Mark Utting
 */
public class FlatRangeSetTest
  extends TestCase
{
  protected Factory factory_ = new Factory();

  protected final double ACCURACY = 0.01;
  protected List emptyList = new ArrayList();
  
  protected BigInteger big9 = new BigInteger("9");
  protected BigInteger big10 = new BigInteger("10");
  protected BigInteger big11 = new BigInteger("11");
  protected BigInteger big12 = new BigInteger("12");
  protected BigInteger big13 = new BigInteger("13");
  // names for integer variables
  protected RefName i = factory_.createRefName("i",emptyList,null);
  protected RefName j = factory_.createRefName("j",emptyList,null);
  protected RefName k = factory_.createRefName("k",emptyList,null);
  // names for set variables
  protected RefName s = factory_.createRefName("s",emptyList,null);
  protected RefName t = factory_.createRefName("t",emptyList,null);
  // integer constant expressions
  protected Expr i9 = factory_.createNumExpr(big9);
  protected Expr i10 = factory_.createNumExpr(big10);
  protected Expr i11 = factory_.createNumExpr(big11);
  protected Expr i12 = factory_.createNumExpr(big12);
  protected Expr i13 = factory_.createNumExpr(big13);

  // several environments used during testing.
  protected Envir envEmpty = new Envir();
  protected Envir envI  = envEmpty.add(i,i10);
  protected Envir envK  = envEmpty.add(k,i12);
  protected Envir envIJK = envEmpty.add(i,i10).add(j,i11).add(k,i12);
  
  // The two EvalSets that we will test.
  // These should be overridden by subclasses...
  protected EvalSet set = new FlatRangeSet(i,k,s);
  protected EvalSet emptySet = new FlatRangeSet(k,j,s);
  
  public void testEmpty()
  {
    Mode m = ((FlatPred)set).chooseMode(envEmpty);
    Assert.assertNull(m);
  }
  
  public void testIOO()
  {
    Mode m = ((FlatPred)set).chooseMode(envI);
    Assert.assertNull(m);
  }
  
  public void testOIO()
  {
    Mode m = ((FlatPred)set).chooseMode(envK);
    Assert.assertNull(m);
  }
  
  public void testEmptySet()
  {
    Mode m = ((FlatPred)emptySet).chooseMode(envIJK);
    Assert.assertTrue(m != null);
    ((FlatPred)emptySet).setMode(m);
    ((FlatPred)emptySet).startEvaluation();
    Assert.assertTrue(((FlatPred)emptySet).nextEvaluation());
    EvalSet tempSet = (EvalSet)m.getEnvir().lookup(s);
    Assert.assertTrue(tempSet != null);
    Assert.assertTrue(tempSet == emptySet);
    Assert.assertEquals(0.0,emptySet.estSize(),ACCURACY);
    Iterator it = tempSet.members();
    Assert.assertTrue(it != null);
    Assert.assertFalse(it.hasNext());
    Assert.assertFalse(emptySet.isMember(i10));
    Assert.assertFalse(emptySet.isMember(i12));
    Assert.assertFalse(((FlatPred)emptySet).nextEvaluation());
  }
  
  public void testII0()
  {
    Mode m = ((FlatPred)set).chooseMode(envIJK);
    Assert.assertTrue(m != null);
    ((FlatPred)set).setMode(m);
    ((FlatPred)set).startEvaluation();
    Assert.assertTrue(((FlatPred)set).nextEvaluation());
    Assert.assertTrue(m.getEnvir().lookup(s) != null);
    //Checking the estSize() method
    Assert.assertEquals(3.0, set.estSize(), ACCURACY);
    //Checking the freeVars() method
    Set temp = set.freeVars();
    Assert.assertTrue(temp.contains(i));
    Assert.assertTrue(temp.contains(k));
    Assert.assertFalse(temp.contains(s));
    //Checking the isMember() method
    Assert.assertFalse(set.isMember(i9));
    Assert.assertTrue(set.isMember(i10));
    Assert.assertTrue(set.isMember(i11));
    Assert.assertTrue(set.isMember(i12));
    Assert.assertFalse(set.isMember(i13));
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
    comparisonSet.add(i11);
    comparisonSet.add(i12);
    //This compares the two HashSets, and checks if they are equal
    Assert.assertTrue(allElements.equals(comparisonSet));
    Assert.assertFalse(((FlatPred)set).nextEvaluation());
  }
  
  /** Tests i..k = t /\ i..k = t. */ 
  public void testIII()
  {
    EvalSet tempRangeSet = new FlatRangeSet(i,k,t);
    FlatPred tempFlat = (FlatPred)tempRangeSet;
    Mode tempMode = tempFlat.chooseMode(envIJK);
    tempFlat.setMode(tempMode);
    tempFlat.startEvaluation();
    tempFlat.nextEvaluation();
    Envir envIJKT = tempFlat.getMode().getEnvir();
    Mode m = ((FlatPred)set).chooseMode(envIJKT);
    Assert.assertTrue(m != null);
    ((FlatPred)set).setMode(m);
    ((FlatPred)set).startEvaluation();
    // Check that the generated set (s) equals t.
    Assert.assertTrue(((FlatPred)set).nextEvaluation());
    Assert.assertFalse(((FlatPred)set).nextEvaluation());
  }
}




