/**
Copyright (C) 2007 Mark Utting
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

import net.sourceforge.czt.animation.eval.ZTestCase;
import nz.ac.waikato.modeljunit.GreedyTester;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the FlatIfThenElse class.
 *
 * @author Mark Utting
 */
public class FlatIfThenElseTest
  extends ZTestCase
{
  private FlatPred pred_;
  private ZName leftName_, rightName_, result_;

  public void setUp()
  {
    zlive_.resetNewNames();
    FlatPredList test = new FlatPredList(zlive_);
    FlatPredList left = new FlatPredList(zlive_);
    FlatPredList right = new FlatPredList(zlive_);
    test.addPred(parsePred("x<y"));
    leftName_ = left.addExpr(parseExpr("x+1"));
    rightName_ = right.addExpr(parseExpr("y*2"));
    result_ = zlive_.createNewName();
    pred_ = new FlatIfThenElse(test, left, leftName_,
        right, rightName_, result_);
  }

  public void testToString()
  {
    assertEquals("(IF x < y\n"
        + "THEN tmp1 == 1;\n"
        + "  "+leftName_+" = x + tmp1\n"
        + "ELSE tmp3 == 2;\n"
        + "  "+rightName_+" = y * tmp3\n"
        + ") = "+result_,
      pred_.toString());
  }

  public void testGood()
  throws FileNotFoundException
  {
    FlatPredModel iut =
      new FlatPredModel(pred_,
        new ZName[] {x,y,result_},
        "IIO,III", // these are the only modes that should work
        new Eval(1, "III", i0, i2, i1),  // THEN x+1
        new Eval(1, "IIO", i4, i4, i8)   // ELSE y*2
    );
    new GreedyTester(iut).generate(200);
  }

  public void testFail()
  throws FileNotFoundException
  {
    FlatPredModel iut =
      new FlatPredModel(pred_,
        new ZName[] {x,y,result_},
        "IIO,III", // these are the only modes that should work
        new Eval(0, "III", i0, i2, i2),  // THEN x+1
        new Eval(1, "IIO", i4, i0, i0)   // ELSE y*2
    );
    new GreedyTester(iut).generate(200);
  }
}




