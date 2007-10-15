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

import java.io.IOException;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;

/** A model of a set with N elements. (N <= 13)
 *  With N=10, this model has 1024 states and 20480 transitions,
 *  which would take a long time to test exhaustively.
 *  See SmartSetAdaptor for a different/better way of testing
 *  large sets.
 */
public class LargeSet implements FsmModel
{
  protected boolean[] elem; // elem[i]==true iff i is in the set

  /** Equivalent to LargeSet(2). 
   *  Which is actually quite a small set!
   */
  public LargeSet()
  {
    this(6);
  }

  /** Construct a model of a set with N elements.
   *
   * @param N  Must be 1..13.
   */
  public LargeSet(int N)
  {
    elem = new boolean[N];
  }

  /** Converts elem into a string of 'T' and 'F' characters. */
  public Object getState()
  {
    // A version of getState() that returns the set cardinality
    /*
    int count = 0;
    for (int i=0; i < elem.length; i++)
      if (elem[i])
        count++;
    return count;
    */

    // A version of getState() that returns the complete TF string
    StringBuffer result = new StringBuffer();
    for (int i=0; i < elem.length; i++)
      result.append(elem[i] ? "T" : "F");
    return result.toString();
  }

  /** Set all bits of elem to false. */
  public void reset(boolean testing)
  {
    for (int i=0; i < elem.length; i++)
      elem[i] = false;
  }

  public void addElem(int i) {elem[i] = true;}
  public void delElem(int i) {elem[i] = false;}

  // TODO: we need parameterized actions to make this convenient.

  // guards for the following add actions
  public boolean add0Guard() {return elem.length > 0;}
  public boolean add1Guard() {return elem.length > 1 && elem[0];}
  public boolean add2Guard() {return elem.length > 2 && elem[0];}
  public boolean add3Guard() {return elem.length > 3 && elem[1];}
  public boolean add4Guard() {return elem.length > 4 && elem[1];}
  public boolean add5Guard() {return elem.length > 5 && elem[2];}
  public boolean add6Guard() {return elem.length > 6 && elem[2];}
  public boolean add7Guard() {return elem.length > 7;}
  public boolean add8Guard() {return elem.length > 8;}
  public boolean add9Guard() {return elem.length > 9;}
  public boolean add10Guard() {return elem.length > 10;}
  public boolean add11Guard() {return elem.length > 11;}
  public boolean add12Guard() {return elem.length > 12;}

  @Action public void add0() {addElem(0);}
  @Action public void add1() {addElem(1);}
  @Action public void add2() {addElem(2);}
  @Action public void add3() {addElem(3);}
  @Action public void add4() {addElem(4);}
  @Action public void add5() {addElem(5);}
  @Action public void add6() {addElem(6);}
  @Action public void add7() {addElem(7);}
  @Action public void add8() {addElem(8);}
  @Action public void add9() {addElem(9);}
  @Action public void add10() {addElem(10);}
  @Action public void add11() {addElem(11);}
  @Action public void add12() {addElem(12);}


  // guards for the following del actions
  public boolean del0Guard() {return elem.length > 0;}
  public boolean del1Guard() {return elem.length > 1;}
  public boolean del2Guard() {return elem.length > 2;}
  public boolean del3Guard() {return elem.length > 3;}
  public boolean del4Guard() {return elem.length > 4;}
  public boolean del5Guard() {return elem.length > 5;}
  public boolean del6Guard() {return elem.length > 6;}
  public boolean del7Guard() {return elem.length > 7;}
  public boolean del8Guard() {return elem.length > 8;}
  public boolean del9Guard() {return elem.length > 9;}
  public boolean del10Guard() {return elem.length > 10;}
  public boolean del11Guard() {return elem.length > 11;}
  public boolean del12Guard() {return elem.length > 12;}

  @Action public void del0() {delElem(0);}
  @Action public void del1() {delElem(1);}
  @Action public void del2() {delElem(2);}
  @Action public void del3() {delElem(3);}
  @Action public void del4() {delElem(4);}
  @Action public void del5() {delElem(5);}
  @Action public void del6() {delElem(6);}
  @Action public void del7() {delElem(7);}
  @Action public void del8() {delElem(8);}
  @Action public void del9() {delElem(9);}
  @Action public void del10() {delElem(10);}
  @Action public void del11() {delElem(11);}
  @Action public void del12() {delElem(12);}


  /** An example of generating tests from this model. */
  public static void main(String[] args) throws IOException
  {
    Tester tester = new GreedyTester(new LargeSet(2));
    tester.buildGraph(100000);
    CoverageHistory hist = new CoverageHistory(new TransitionCoverage(), 1);
    tester.addCoverageMetric(hist);
    tester.addListener("verbose");
    while (hist.getPercentage() < 99.0)
      tester.generate();
    System.out.println("Transition Coverage ="+hist.toString());
    System.out.println("History = "+hist.toCSV());
  }
}
