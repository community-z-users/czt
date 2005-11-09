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
import net.sourceforge.czt.animation.eval.flatpred.*;


/**
 * A (JUnit) test class for testing subclasses of EvalSet.
 *
 * @author Mark Utting
 */
public class EvalSetTest
  extends ZTestCase
{
  // names for integer variables
  protected ZRefName i = factory_.createZRefName("i");
  protected ZRefName j = factory_.createZRefName("j");
  protected ZRefName k = factory_.createZRefName("k");
  // names for set variables
  protected ZRefName s = factory_.createZRefName("s");
  protected ZRefName t = factory_.createZRefName("t");

  // several environments used during testing.
  protected Envir envEmpty = new Envir();
  protected Envir envI  = envEmpty.add(i,i10);
  protected Envir envJ  = envEmpty.add(j,i11);
  protected Envir envK  = envEmpty.add(k,i12);
  protected Envir envIJK = envEmpty.add(i,i10).add(j,i11).add(k,i12);

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

  public void setUp()
  {
    set = new FlatPredList(zlive_);
    set.add(new FlatRangeSet(i,k,s));
    
    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatDiscreteSet(new ArrayList<ZRefName>(),s));
  }
  
  /** @return Bounds for i,j,k only. */
  protected Bounds getBounds()
  {
    Bounds bnds = new Bounds();
    bnds.addLower(i,new BigInteger("10"));
    bnds.addUpper(i,new BigInteger("10"));
    bnds.addLower(j,new BigInteger("11"));
    bnds.addUpper(j,new BigInteger("11"));
    bnds.addLower(k,new BigInteger("12"));
    bnds.addUpper(k,new BigInteger("12"));
    return bnds;
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
    EvalSet resultSet = (EvalSet) m.getEnvir().lookup(s);
    Assert.assertTrue(resultSet != null);
    Assert.assertEquals(0.0,resultSet.estSize(),ACCURACY);
    Iterator it = resultSet.members();
    Assert.assertTrue(it != null);
    Assert.assertFalse(it.hasNext());
    Assert.assertFalse(resultSet.isMember(i10));
    Assert.assertFalse(resultSet.isMember(i12));
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
    Assert.assertFalse(resultSet.isMember(i9));
    Assert.assertTrue(resultSet.isMember(i10));
    Assert.assertTrue(resultSet.isMember(i11));
    Assert.assertTrue(resultSet.isMember(i12));
    Assert.assertFalse(resultSet.isMember(i13));
    //Checking the members() method
    Set<Expr> allElements = new HashSet<Expr>();
    Iterator<Expr> it = resultSet.members();
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




