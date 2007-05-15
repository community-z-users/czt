/**
Copyright (C) 2006 Mark Utting
This file is part of the czt project.

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

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.modeljunit.ModelTestCase;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatBindingTest
  extends ZTestCase
{
  public void testEmpty()
  {
    BindExpr bind = (BindExpr) this.parseExpr("\\lblot \\rblot");
    List<ZName>  names = new ArrayList<ZName>();
    List<ZName> exprs = new ArrayList<ZName>();
    FlatPred pred = new FlatBinding(names,exprs,z);
    assertEquals("<|  |> = z", pred.toString());

    FlatPredModel iut = new FlatPredModel(pred, new ZName[] {z},
                            "OOO,OII,IOI,IIO,III",
                            new Eval(1, "O", bind),
                            new Eval(1, "I", bind)
                            );
    ModelTestCase model = new ModelTestCase(iut);
    model.randomWalk(1500);
  }

  public void testMBT()
  {
    BindExpr bind = (BindExpr) this.parseExpr("\\lblot x==3, y==4 \\rblot");
    List<ZName>  names = new ArrayList<ZName>();
    names.add( ((ConstDecl) bind.getZDeclList().get(0)).getZName());
    names.add( ((ConstDecl) bind.getZDeclList().get(1)).getZName());
    List<ZName> exprs = new ArrayList<ZName>();
    exprs.add(x);
    exprs.add(y);
    FlatPred pred = new FlatBinding(names,exprs,z);
    assertEquals("<| x==x, y==y |> = z", pred.toString());

    FlatPredModel iut = new FlatPredModel(pred, new ZName[] {x,y,z},
                            "OII,IOI,IIO,III",
                            new Eval(1, "???", i3, i4, bind),
                            new Eval(0, "I?I", i2, i5, bind)
                            );
    ModelTestCase model = new ModelTestCase(iut);
    /*
    int interval = 2;
    CoverageHistory actions = new CoverageHistory(new ActionCoverage(), interval);
    CoverageHistory states = new CoverageHistory(new StateCoverage(), interval);
    CoverageHistory trans = new CoverageHistory(new TransitionCoverage(), interval);
    CoverageHistory tpair = new CoverageHistory(new TransitionPairCoverage(), interval);
    addCoverageMetric(actions);
    addCoverageMetric(states);
    addCoverageMetric(trans);
    addCoverageMetric(tpair);
    */
    model.randomWalk(1500);

    /*
    // We print a vertical table of coverage statistics.
    // First we build the graph, so we get more accurate stats
    // (this also adds some transitions to the end of the history).
    fsmBuildGraph(iut);
    int minlen = Integer.MAX_VALUE;
    List<List<Integer>> table = new ArrayList<List<Integer>>();
    System.out.print("Transitions");
    for (CoverageMetric cm : getCoverageMetrics()) {
      if (cm instanceof CoverageHistory) {
        System.out.print(","+cm.getName()+"="+cm);
        List<Integer> history = ((CoverageHistory)cm).getHistory();
        table.add(history);
        if (history.size() < minlen)
          minlen = history.size();
      }
    }
    System.out.println();
    for (int i=0; i < minlen; i++) {
      System.out.print(i*interval);
      for (List<Integer> hist : table)
        System.out.print(","+hist.get(i));
      System.out.println();
    }
    */
  }
}




