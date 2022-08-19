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

import java.io.FileNotFoundException;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import nz.ac.waikato.modeljunit.GreedyTester;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the FlatOr class.
 *
 * @author Mark Utting
 */
public class FlatOrTest
  extends ZTestCase
{
  private FlatPred pred;

  public void setUp()
  {
    zlive_.resetNewNames();
    FlatPredList left = new FlatPredList(zlive_);
    left.addPred(parsePred("z=x"));
    //    System.out.println("left.args="+left.getArgs());
    Assert.assertEquals(2, left.getArgs().size());
    Assert.assertEquals(x, left.getArgs().get(0));
    Assert.assertEquals(z, left.getArgs().get(1));

    FlatPredList right = new FlatPredList(zlive_);
    right.addPred(parsePred("z \\in \\{x+1,y+1\\}"));
    //    System.out.println("right.args="+right.getArgs());
    Assert.assertEquals(3, right.getArgs().size());
    Assert.assertEquals(x, right.getArgs().get(0));
    Assert.assertEquals(y, right.getArgs().get(1));
    Assert.assertEquals(z, right.getArgs().get(2));

    pred = new FlatOr(left, right);
    //    System.out.println("pred.args="+pred.getArgs());
    Assert.assertEquals(3, pred.getArgs().size());
    Assert.assertEquals(x, pred.getArgs().get(0));
    Assert.assertEquals(y, pred.getArgs().get(1));
    Assert.assertEquals(z, pred.getArgs().get(2));
  }

  public void testToString()
  {
    assertEquals("( z = x\n) \\/ ( tmp1 == 1;\n"
               + "  tmp0 = x + tmp1;\n"
               + "  tmp3 == 1;\n"
               + "  tmp2 = y + tmp3;\n"
               + "  tmp4 = { tmp2, tmp0 };\n"
               + "  z in tmp4 :: 1000.0 \n"
               + ")",
               pred.toString());
  }

  public void testOr1()
  throws FileNotFoundException
  {
    FlatPredModel iut =
      new FlatPredModel(pred,
        new ZName[] {x,y,z},
        "IIO,III", // these are the only modes that should work
        new Eval(1, "III", i2, i3, i2),  // only z=x is true
        new Eval(3, "IIO", i2, i4, i0)   // ie. z in {2,3,5}
    );
    new GreedyTester(iut).generate(200);
  }
  
  /** Tests that z takes the correct three values.
   *  (Because FlatPredModel checks the number of solutions, 
   *  but not the values with the output environments.) */
  public void testZValues()
  throws FileNotFoundException
  {
    Bounds bnds = new Bounds(null);
    pred.inferBounds(bnds);
    Envir env0 = new Envir().plus(x, i2).plus(y, i4);
    Mode mode = pred.chooseMode(env0);
    Envir env = mode.getEnvir();
    assertTrue(env.isDefinedSince(env0, z));
    assertNotNull(mode);
    pred.setMode(mode);
    pred.startEvaluation();
    assertTrue(pred.nextEvaluation());
    assertEquals(i2, env.lookup(z));
    assertTrue(pred.nextEvaluation());
    assertEquals(i3, env.lookup(z));
    assertTrue(pred.nextEvaluation());
    assertEquals(i5, env.lookup(z));
    assertFalse(pred.nextEvaluation());
  }
}




