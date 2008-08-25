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

import java.util.HashSet;
import java.util.Set;

import junit.framework.Assert;
import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;

/** This class shows how we can use inheritance to add adaptor code.
 *  That is, it subclasses the SimpleSet model and adds
 *  adaptor code that links the model to a system under test (SUT).
 *  <p>
 *  It does a little more than just this, because I decided that I
 *  wanted to test a set with more than 12 elements (to force HashSet
 *  to expand at least once).  So in this adaptor
 *  class, the s1 flag models the presence/absence of the empty string "",
 *  while the s2 flag models the presence/absence of TWELVE other strings
 *  "s1".."s12".  This means that those strings are always added or
 *  deleted as a group, so our model stays small (4 states and 16 transitions)
 *  so is easy and quick to test thoroughly.  This is an example of 
 *  abstraction -- where the model takes a simplified view (the s2 boolean)
 *  of a more complex situation in the SUT (twelve strings).
 */
public class SmartSetAdaptor extends SimpleSet
{
  protected final int S2_STRINGS = 12;

  protected Set<String> sut_;

  public SmartSetAdaptor(Set<String> sut)
  {
    sut_ = sut;
  }

  @Override
  public void reset(boolean testing)
  {
    super.reset(testing);
    sut_.clear();
  }

  @Action public void addS1()
  {
    super.addS1();
    sut_.add("");
    checkSUT();
  }
  
  @Action public void addS2()
  {
    super.addS2();
    for (int i=1; i<=S2_STRINGS; i++)
      sut_.add("s"+i);
    checkSUT();
  }
  
  @Action public void removeS1()
  {
    super.removeS1();
    sut_.remove("");
    checkSUT();
  }
  
  @Action public void removeS2()
  {
    super.removeS2();
    for (int i=1; i<=S2_STRINGS; i++)
      sut_.remove("s"+i);
    checkSUT();
  }

  /** Check that the SUT is in the expected state. */
  protected void checkSUT()
  {
    int size = (s1 ? 1 : 0) + (s2 ? S2_STRINGS : 0);
    Assert.assertEquals(size, sut_.size());
    Assert.assertEquals(s1, sut_.contains(""));
    Assert.assertEquals(s2, sut_.contains("s1")); // check the first one
    Assert.assertEquals(s2, sut_.contains("s"+S2_STRINGS)); // check last one
  }

  /** An example of generating tests from this model.
   *  This method would typically be written as a JUnit test method,
   *  but we write it as main so that it is easy to run.
   */
  public static void main(String[] args)
  {
    Set<String> sut = new HashSet<String>();
    Tester tester = new GreedyTester(new SmartSetAdaptor(sut));
    tester.addListener("verbose");
    tester.generate(100);
  }
}
