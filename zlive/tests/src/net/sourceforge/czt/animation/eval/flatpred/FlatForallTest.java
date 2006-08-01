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
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZRefName;


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
    // We have to typecheck it, so that ZRefNames are bound to ZDeclNames.
    SchExpr e = (SchExpr) parseExpr("[x,y,z:\nat | \\forall i:x \\upto y @ i > z]");
    TypeCheckUtils.typecheck(e, new SectionManager());
    ForallPred all = (ForallPred) e.getZSchText().getPred();
    FlatPredList stext = new FlatPredList(zlive_);
    stext.addDecl(all.getZSchText().getZDeclList().get(0));
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(all.getPred());
    sut_ = new FlatForall(stext, body);
  }

  public void testFreeVars()
  {
    System.out.println("FlatForall freevars="+sut_.freeVars());
    assertEquals(3, sut_.freeVars().size());  // x,y and z
  }

  public void testSimple()
  {
    FlatPredModel iut =
      new FlatPredModel(sut_,
        new ZRefName[] {x,y,z},
        "III", // this is the only mode that should work
        new Eval(1, "III", i2, i4, i1), // i:2..4 @ i>1
        new Eval(0, "III", i2, i4, i2)  // i:2..4 @ i>2
    );
    ModelTestCase model = new ModelTestCase(iut);
    model.randomWalk(200);
  }

  /** Test an empty range. */
  public void testEmpty()
  {
    FlatPredModel iut =
      new FlatPredModel(sut_,
        new ZRefName[] {x,y,z},
        "III", // this is the only mode that should work
        new Eval(1, "III", i2, i1, i0), // i:2..1 is empty
        new Eval(1, "III", i2, i0, i4)  // i:2..0 @ i>4
    );
    ModelTestCase model = new ModelTestCase(iut);
    model.randomWalk(200);
  }
}
