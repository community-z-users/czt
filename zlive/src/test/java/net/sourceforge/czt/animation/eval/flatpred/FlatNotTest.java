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
import net.sourceforge.czt.animation.eval.ZTestCase;
import nz.ac.waikato.modeljunit.GreedyTester;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the FlatOr class.
 *
 * @author Mark Utting
 */
public class FlatNotTest
  extends ZTestCase
{
  public void testToString()
  {
    FlatPredList pred = new FlatNot(zlive_);
    pred.addPred(parsePred("x=y"));
    pred.addPred(parsePred("y=z"));
    assertEquals("not (x = y;\n  y = z\n)", pred.toString());
  }

  public void testNot1()
  throws FileNotFoundException
  {
    FlatPredList pred = new FlatNot(zlive_);
    pred.addPred(parsePred("x=y"));
    pred.addPred(parsePred("y=z"));
    //    System.out.println("left.args="+left.getArgs());
    Assert.assertEquals(3, pred.getArgs().size());

    FlatPredModel iut =
      new FlatPredModel(pred,
        new ZName[] {x,y,z},
        "III", // these are the only modes that should work
        new Eval(0, "III", i2, i2, i2),  // x=y=z is true, so not is false
        new Eval(1, "III", i2, i2, i3)   // not is true
    );
    new GreedyTester(iut).generate(200);
  }
}




