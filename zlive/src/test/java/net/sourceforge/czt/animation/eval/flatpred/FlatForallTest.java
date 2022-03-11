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

import net.sourceforge.czt.animation.eval.ZTestCase;
import nz.ac.waikato.modeljunit.GreedyTester;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.session.Dialect;


/**
 * A (JUnit) test class for testing the FlatOr class.
 *
 * @author Mark Utting
 */
public class FlatForallTest
  extends ZTestCase
{
  protected FlatForall sut_;

  @Override public void setUp()
  {
    // We put the forall into a context so that we can typecheck it.
    // We have to typecheck it, so that ZNames are bound to ZDeclNames.
    zlive_.resetNewNames();
    SchExpr e = (SchExpr) parseExpr("[x,y,z:\\nat | \\forall i:x \\upto y @ i > z]");
    TypeCheckUtils.typecheck(e, new SectionManager(Dialect.ZPATT));
    ForallPred all = (ForallPred) e.getZSchText().getPred();
    FlatPredList stext = new FlatPredList(zlive_);
    stext.addDecl(all.getZSchText().getZDeclList().get(0));
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(all.getPred());
    sut_ = new FlatForall(stext, body);
  }

  public void testToString()
  {
    assertEquals("(forall\n  tmp0 = x .. y;\n  i in tmp0 :: 1000.0 \n@ z < i\n)", sut_.toString());
  }

  public void testFreeVars()
  {
    assertEquals(3, sut_.freeVars().size());  // x,y and z
  }

  public void testSimple()
  {
    FlatPredModel iut =
      new FlatPredModel(sut_,
        new ZName[] {x,y,z},
        "III", // this is the only mode that should work
        new Eval(1, "III", i2, i4, i1), // i:2..4 @ i>1
        new Eval(0, "III", i2, i4, i2)  // i:2..4 @ i>2
    );
    new GreedyTester(iut).generate(200);
  }

  /** Test an empty range. */
  public void testEmpty()
  {
    FlatPredModel iut =
      new FlatPredModel(sut_,
        new ZName[] {x,y,z},
        "III", // this is the only mode that should work
        new Eval(1, "III", i2, i1, i0), // i:2..1 is empty
        new Eval(1, "III", i2, i0, i4)  // i:2..0 @ i>4
    );
    new GreedyTester(iut).generate(200);
  }
}
