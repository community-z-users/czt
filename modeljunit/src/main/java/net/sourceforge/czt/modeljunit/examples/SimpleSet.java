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

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;

/** A model of a set with two elements: s1 and s2. */
public class SimpleSet implements FsmModel
{
  protected boolean s1, s2;

  public Object getState()
  { return (s1 ? "T" : "F") + (s2 ? "T" : "F"); }

  public void reset(boolean testing)
  { s1 = false; s2 = false; }

  @Action public void addS1() {s1 = true;}
  @Action public void addS2() {s2 = true;}
  @Action public void removeS1() {s1 = false;}
  @Action public void removeS2() {s2 = false;} // or {s2 = 1/0>0;} to see an error
  //@Action public void clear() {s1 = false; s2 = false;}

  /** An example of generating tests from this model. */
  public static void main(String[] args)
  {
    Tester tester = new GreedyTester(new SimpleSet());
    tester.addListener(new VerboseListener());
    tester.generate(100);
  }
}
