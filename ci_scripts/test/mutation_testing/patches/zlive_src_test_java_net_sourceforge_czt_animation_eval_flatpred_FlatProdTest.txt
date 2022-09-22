/**
Copyright (C) 2005 Mark Utting
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

import java.io.FileNotFoundException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.animation.eval.result.DiscreteSet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import nz.ac.waikato.modeljunit.GreedyTester;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatProdTest
  extends ZTestCase
{
  private FlatPred pred_;
  
  public void setUp()
  {
    List<ZName> args = new ArrayList<ZName>();
    args.add(x);
    args.add(y);
    pred_ = new FlatProd(args,z);
  }

  public void testToString()
  {
    assertEquals("z = x x y", pred_.toString());
  }

  public void testProd()
  throws FileNotFoundException
  {
    RangeSet r0_1 = new RangeSet(BigInteger.ZERO, BigInteger.ONE);
    RangeSet r1_0 = new RangeSet(BigInteger.ONE, BigInteger.ZERO);
    DiscreteSet empty = new DiscreteSet();
    DiscreteSet four = new DiscreteSet();
    four.add(parseExpr("(0,0)"));
    four.add(parseExpr("(0,1)"));
    four.add(parseExpr("(1,0)"));
    four.add(parseExpr("(1,1)"));
    
    FlatPredModel iut =
      new FlatPredModel(pred_, new ZName[] {x,y,z},
          "IIO,III",
          new Eval(1, "II?", r0_1, r0_1, four),
          new Eval(1, "II?", r0_1, r1_0, empty)
      );
    new GreedyTester(iut).generate(1500);
  }
}




