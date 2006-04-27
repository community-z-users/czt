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
import net.sourceforge.czt.modeljunit.ModelTestCase;
import net.sourceforge.czt.z.ast.ZRefName;


/**
 * A (JUnit) test class for testing the FlatOr class.
 *
 * @author Mark Utting
 */
public class FlatOrTest
  extends ZTestCase
{
  public void testOr1()
  throws FileNotFoundException
  {
    FlatPredList left = new FlatPredList(zlive_);
    left.addPred(parsePred("z=x"));
    System.out.println("left.args="+left.getArgs());
    Assert.assertEquals(2, left.getArgs().size());
    Assert.assertEquals(x, left.getArgs().get(0));
    Assert.assertEquals(z, left.getArgs().get(1));
    FlatPredList right = new FlatPredList(zlive_);
    right.addPred(parsePred("z \\in \\{x+1,y+1\\}"));
    System.out.println("right.args="+right.getArgs());
    Assert.assertEquals(3, right.getArgs().size());
    Assert.assertEquals(x, right.getArgs().get(0));
    Assert.assertEquals(y, right.getArgs().get(1));
    Assert.assertEquals(z, right.getArgs().get(2));
    FlatPred pred = new FlatOr(left, right);
    System.out.println("pred.args="+pred.getArgs());
    Assert.assertEquals(3, pred.getArgs().size());
    Assert.assertEquals(x, pred.getArgs().get(0));
    Assert.assertEquals(y, pred.getArgs().get(1));
    Assert.assertEquals(z, pred.getArgs().get(2));

    FlatPredModel iut =
      new FlatPredModel(pred,
        new ZRefName[] {x,y,z},
        "IIO,III", // these are the only modes that should work
        new Eval(1, "III", i2, i3, i2),  // only z=x is true
        new Eval(3, "IIO", i2, i4, i0)   // ie. x in {2,3,5}
    );
    ModelTestCase model = new ModelTestCase(iut);
    model.randomWalk(200);
  }
}




