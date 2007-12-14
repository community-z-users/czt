/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.examples.SimpleSet;
import junit.framework.TestCase;

/**
 *  Unit tests for the lookahead tester.
 * @author marku
 *
 */
public class LookaheadTesterTest extends TestCase
{
  protected LookaheadTester tester;
  protected List<Transition> path;
  protected CoverageMetric transitions;

  public void setUp()
  {
    tester = new LookaheadTester(new SimpleSet());
    transitions = tester.addCoverageMetric(new TransitionCoverage());
    path = new ArrayList<Transition>();
    tester.addListener(new AbstractListener() {
      public String getName()
      {
        return "path listener";
      }
      public void doneTransition(int action, Transition tr)
      {
        path.add(tr);
        //System.out.println(path.size());
      }
    }
    );
  }

  public void testGetDepth()
  {
    assertEquals(3, tester.getDepth());
  }

  public void testSetDepth()
  {
    tester.setDepth(10);
    assertEquals(10, tester.getDepth());
    tester.setDepth(1);
    assertEquals(1, tester.getDepth());
  }

  public void testGraph() throws FileNotFoundException
  {
    Tester test = new GreedyTester(new SimpleSet());
    GraphListener graph = (GraphListener) test.addListener("graph");
    test.buildGraph();
    graph.printGraphDot("quidonc.dot");
  }

  public void testGenerate1()
  {
    tester.setDepth(1);
    tester.setNewActionValue(tester.getNewTransValue());
    tester.generate(17);
    // impressive: this covers all 16 transitions with a walk of just 17.
    assertEquals(17, path.size());
    assertEquals("(FF, addS1, TF)", path.get(0).toString());
    assertEquals("(TF, addS1, TF)", path.get(1).toString());
    assertEquals("(TF, addS2, TT)", path.get(2).toString());
    assertEquals("(TT, addS1, TT)", path.get(3).toString());
    assertEquals("(TT, addS2, TT)", path.get(4).toString());
    assertEquals("(TT, delS1, FT)", path.get(5).toString());
    assertEquals("(FT, addS1, TT)", path.get(6).toString());
    assertEquals("(TT, delS2, TF)", path.get(7).toString());
    assertEquals("(TF, delS1, FF)", path.get(8).toString());
    assertEquals("(FF, addS2, FT)", path.get(9).toString());
    assertEquals("(FT, addS2, FT)", path.get(10).toString());
    assertEquals("(FT, delS1, FT)", path.get(11).toString());
    assertEquals("(FT, delS2, FF)", path.get(12).toString());
    assertEquals("(FF, delS1, FF)", path.get(13).toString());
    assertEquals("(FF, delS2, FF)", path.get(14).toString());
    assertEquals("(FF, addS1, TF)", path.get(15).toString());
    assertEquals("(TF, delS2, TF)", path.get(16).toString());
    assertEquals(16, transitions.getCoverage());
  }


  public void testGenerate2()
  {
    tester.setDepth(3);
    tester.generate(19);
    // 
    assertEquals(19, path.size());
    assertEquals("(FF, addS1, TF)", path.get(0).toString());
    assertEquals("(TF, addS2, TT)", path.get(1).toString());
    assertEquals("(TT, delS1, FT)", path.get(2).toString());
    assertEquals("(FT, delS2, FF)", path.get(3).toString());
    assertEquals("(FF, addS2, FT)", path.get(4).toString());
    assertEquals("(FT, addS1, TT)", path.get(5).toString());
    assertEquals("(TT, addS1, TT)", path.get(6).toString());
    assertEquals("(TT, addS2, TT)", path.get(7).toString());
    assertEquals("(TT, delS2, TF)", path.get(8).toString());
    
    assertEquals("(TF, addS1, TF)", path.get(9).toString());
    assertEquals("(TF, delS1, FF)", path.get(10).toString());
    assertEquals("(FF, delS1, FF)", path.get(11).toString());
    assertEquals("(FF, delS2, FF)", path.get(12).toString());
    
    assertEquals("(FF, addS1, TF)", path.get(13).toString());
    assertEquals("(TF, delS2, TF)", path.get(14).toString());
    
    assertEquals("(TF, addS2, TT)", path.get(15).toString());
    assertEquals("(TT, delS1, FT)", path.get(16).toString());
    assertEquals("(FT, addS2, FT)", path.get(17).toString());
    assertEquals("(FT, delS1, FT)", path.get(18).toString());
    assertEquals(16, transitions.getCoverage());
  }
}
