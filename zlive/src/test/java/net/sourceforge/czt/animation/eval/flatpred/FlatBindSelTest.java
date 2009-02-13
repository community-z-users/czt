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

package net.sourceforge.czt.animation.eval.flatpred;

import java.io.FileNotFoundException;

import net.sourceforge.czt.animation.eval.ZTestCase;
import nz.ac.waikato.modeljunit.GreedyTester;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing binding.name = value.
 *
 * @author Mark Utting
 */
public class FlatBindSelTest
  extends ZTestCase
{
  public void testToString()
  {
    FlatPred pred = new FlatBindSel(x,y,z);
    assertEquals("z = x.y", pred.toString());
  }

  public void testMBT()
  throws FileNotFoundException
  {
    FlatPred pred = new FlatBindSel(x,y,z);
    Expr binding = parseExpr("\\lblot x==2,y==3 \\rblot");
    
    FlatPredModel iut =
      new FlatPredModel(pred, new ZName[] {x,z},
          "IOO,IOI,IIO,III",
          new Eval(1, "I?", binding, i3),
          new Eval(0, "II", binding, i5)  // should fail
      );
    GreedyTester tester = new GreedyTester(iut);
    tester.generate(300);
  }
}




