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

package net.sourceforge.czt.animation.eval;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatDiscreteSet;
import net.sourceforge.czt.animation.eval.flatpred.FlatPred;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.flatpred.FlatRangeSet;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing subclasses of EvalSet.
 *
 * @author Mark Utting
 */
public class EvalSetTest
  extends ZTestCase
{
  // names for integer variables
  protected ZName i = factory_.createZName("i");
  protected ZName j = factory_.createZName("j");
  protected ZName k = factory_.createZName("k");
  // names for set variables
  protected ZName es = factory_.createZName("es"); // empty set
  protected ZName s = factory_.createZName("s");
  protected ZName t = factory_.createZName("t");

  // several environments used during testing.
  protected Envir envEmpty = new Envir();
  protected Envir envI  = envEmpty.plus(i,i10);
  protected Envir envJ  = envEmpty.plus(j,i11);
  protected Envir envK  = envEmpty.plus(k,i12);
  protected Envir envIJK = envEmpty.plus(i,i10).plus(j,i11).plus(k,i12);

  // The two EvalSets that we will test.
  /** Subclasses must initialise this FlatPredList so that it
   *  calculates some set called s that contains
   *  just 10, 11 and 12 (or i,j,k, respectively).
   *  The resulting set must be the last entry in the FlatPredList.
   */
  protected FlatPredList set;

  /** Subclasses must initialise this FlatPredList so that it
   *  calculates an empty set called s.
   *  The resulting set must be the last entry in the FlatPredList.
   */
  protected FlatPredList emptySet;

  protected Bounds bounds_;
  
  public void setUp()
  {
    bounds_ = new Bounds(); // starts empty
    
    set = new FlatPredList(zlive_);
    set.add(new FlatRangeSet(i,k,s));
    set.inferBoundsFixPoint(bounds_);

    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatDiscreteSet(new ArrayList<ZName>(),es));
    emptySet.inferBoundsFixPoint(bounds_);
  }

  /** Sets the Bounds for i,j,k to 10,11,12, respectively. */
  protected void setIJKBounds()
  {
    bounds_.addLower(i,new BigInteger("10"));
    bounds_.addUpper(i,new BigInteger("10"));
    bounds_.addLower(j,new BigInteger("11"));
    bounds_.addUpper(j,new BigInteger("11"));
    bounds_.addLower(k,new BigInteger("12"));
    bounds_.addUpper(k,new BigInteger("12"));
  }

  public void testEmpty()
  {
    Mode m = set.chooseMode(envEmpty);
    Assert.assertNull(m);
  }

  public void testIOO()
  {
    Mode m = set.chooseMode(envI);
    Assert.assertNull(m);
  }

  public void testOIO()
  {
    Mode m = set.chooseMode(envK);
    Assert.assertNull(m);
  }

  public void testEmptySet()
  {
    Mode m = emptySet.chooseMode(envIJK);
    Assert.assertTrue(m != null);
    emptySet.setMode(m);
    emptySet.startEvaluation();
    Assert.assertTrue(emptySet.nextEvaluation());
    EvalSet resultSet = (EvalSet) m.getEnvir().lookup(es);
    Assert.assertTrue(resultSet != null);
    Assert.assertEquals(0.0,resultSet.estSize(),ACCURACY);
    Iterator it = resultSet.iterator();
    Assert.assertTrue(it != null);
    Assert.assertFalse(it.hasNext());
    Assert.assertFalse(resultSet.contains(i10));
    Assert.assertFalse(resultSet.contains(i12));
    Assert.assertFalse(emptySet.nextEvaluation());
  }

  public void testII0()
  {
    Mode m = set.chooseMode(envIJK);
    Assert.assertTrue(m != null);
    set.setMode(m);
    set.startEvaluation();
    Assert.assertTrue(set.nextEvaluation());
    EvalSet resultSet = (EvalSet) m.getEnvir().lookup(s);
    Assert.assertTrue(resultSet != null);
    // Checking the estSize() method
    // Some implementations may return a bit more than the true size.
    Assert.assertTrue(3.0 <= resultSet.estSize());
    Assert.assertTrue(resultSet.estSize() <= 4.0);
    //Checking the freeVars() method
    //Some subclasses may not use j.
    Set temp = set.freeVars();
    Assert.assertTrue(temp.contains(i));
    Assert.assertTrue(temp.contains(k));
    Assert.assertTrue(temp.contains(s));
    //Checking the isMember() method
    Assert.assertFalse(resultSet.contains(i9));
    Assert.assertTrue(resultSet.contains(i10));
    Assert.assertTrue(resultSet.contains(i11));
    Assert.assertTrue(resultSet.contains(i12));
    Assert.assertFalse(resultSet.contains(i13));
    //Checking the members() method
    Set<Expr> allElements = new HashSet<Expr>();
    Iterator<Expr> it = resultSet.iterator();
    //All the elements of in the set are added to a HashSet
    while (it.hasNext())
      allElements.add(it.next());
    //Another HashSet named comparisonSet is being created which contains
    //the same elements as the allElements should contain logically
    Set<Expr> comparisonSet = new HashSet<Expr>();
    comparisonSet.add(i10);
    comparisonSet.add(i11);
    comparisonSet.add(i12);
    //This compares the two HashSets, and checks if they are equal
    Assert.assertTrue(allElements.equals(comparisonSet));
    Assert.assertFalse(set.nextEvaluation());
  }

  /** Tests t := i..k, then i..k == t. */
  public void testIII()
  {
    EvalSet tempRangeSet = new FlatRangeSet(i,k,t);
    FlatPred tempFlat = (FlatPred)tempRangeSet;
    Assert.assertNotNull(bounds_);
    tempFlat.inferBounds(bounds_); // bounds_ is empty
    Mode tempMode = tempFlat.chooseMode(envIJK);
    tempFlat.setMode(tempMode);
    tempFlat.startEvaluation();
    tempFlat.nextEvaluation();
    Envir envIJKT = tempFlat.getMode().getEnvir();
    Mode m = set.chooseMode(envIJKT);
    Assert.assertTrue(m != null);
    set.setMode(m);
    set.startEvaluation();
    // Check that the generated set (s) equals t.
    Assert.assertTrue(set.nextEvaluation());
    Assert.assertFalse(set.nextEvaluation());
  }
}




