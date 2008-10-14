/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit.examples;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import junit.framework.Assert;
import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.StopOnFailureListener;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;

/** A model of a set with two elements: s1 and s2.
 *
 *  This model includes the adaptor/harness code that interacts with a
 *  system under test (SUT), which can be any implementation of Set<String>.
 *  The SUT must be passed to the constructor of this class.
 *
 *  After each transition, we call checkSUT(), which uses JUnit Assert
 *  methods to check that the SUT is in the expected state.
 *  (To see a test fail, either pass an instance of StringSetBuggy
 *  to the constructor, or change the "false" in removeS2 to "true").
 *
 *  Note: We could have added this adaptor code by inheriting from the
 *  SimpleSet model, but in this example the model code and the
 *  adaptor code are written in the same class, so that you can see
 *  them side-by-side.
 */
public class SimpleSetWithAdaptor implements FsmModel
{
  protected Set<String> sut_;
  protected boolean s1, s2;

  // our test data for the SUT
  protected String str1 = "some string";
  protected String str2 = "";  // empty string

  /** Tests a StringSet implementation. */
  public SimpleSetWithAdaptor()
  {
    sut_ = new StringSet();
  }

  public SimpleSetWithAdaptor(Set<String> sut)
  {
    sut_ = sut;
  }

  public Object getState()
  {
    return (s1 ? "T" : "F") + (s2 ? "T" : "F");
  }

  public void reset(boolean testing)
  {
    s1 = false;
    s2 = false;
    sut_.clear();
  }

  @Action public void addS1()
  {
    s1 = true;
    sut_.add(str1);
    checkSUT();
  }

  @Action public void addS2()
  {
    // this one shows how we can test the result of sut_.add(...)
    Assert.assertEquals(!s2, sut_.add(str2));
    //sut_.add(str2);
    s2 = true;
    checkSUT();
  }

  @Action public void removeS1()
  {
    s1 = false;
    sut_.remove(str1);
    checkSUT();
  }

  @Action public void removeS2()
  {
    // this one shows how we can test the result of sut_.remove(...)
    Assert.assertEquals(s2, sut_.remove(str2));
    //sut_.remove(str2);
    s2 = false;
    checkSUT();
  }

  /** Check that the SUT is in the expected state. */
  protected void checkSUT()
  {
    int size = (s1 ? 1 : 0) + (s2 ? 1 : 0);
    Assert.assertEquals(size, sut_.size());
    Assert.assertEquals(s1, sut_.contains(str1));
    Assert.assertEquals(s2, sut_.contains(str2));
    Assert.assertEquals(!s1 && !s2, sut_.isEmpty());
    Assert.assertEquals(!s1 && s2, sut_.equals(Collections.singleton(str2)));
  }

  /** An example of generating tests from this model. */
  public static void main(String[] args)
  {
    Set<String> sut = new StringSetBuggy(); // StringSetBuggy();
    Tester tester = new GreedyTester(new SimpleSetWithAdaptor(sut));
    //tester.buildGraph(); // to get better statistics
    tester.addListener(new VerboseListener());
    
    // uncoment this line if you want to stop when the first error is found.
    // tester.addListener(new StopOnFailureListener());
    
    tester.addCoverageMetric(new TransitionCoverage());
    tester.generate(50);
    tester.printCoverage();
  }
}
