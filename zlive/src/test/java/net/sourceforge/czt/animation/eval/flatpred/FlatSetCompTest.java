/**
Copyright (C) 2004 Mark Utting
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

import java.util.Set;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.EvalSetTest;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the FlatSetComp class.
 * This overrides set and emptySet to be FlatSetComp objects.
 *
 * @author Mark Utting
 */
public class FlatSetCompTest
  extends EvalSetTest
{
  protected String setCompStr = "\\{ r : i \\upto k @ r \\}";
  protected String emptySetCompStr = "\\{ r : k \\upto i | r \\in \\{9\\} @ r \\}";

  public FlatSetCompTest()
  {
  }

  public void setUp()
  {
    super.setUp();
    zlive_.resetNewNames(); // so that set and emptyset use known tmp names.
    setIJKBounds();
    SetCompExpr setComp = (SetCompExpr) parseExpr(setCompStr);
    SetCompExpr emptySetComp = (SetCompExpr) parseExpr(emptySetCompStr);
    set = new FlatPredList(zlive_);
    set.add(new FlatSetComp(zlive_,
        setComp.getZSchText(),
        setComp.getExpr(),
        s));
    set.inferBounds(bounds_);

    emptySet = new FlatPredList(zlive_);
    emptySet.add(new FlatSetComp(zlive_,
        emptySetComp.getZSchText(),
        emptySetComp.getExpr(),
        es));
    emptySet.inferBounds(bounds_);
  }

  public void testToString()
  {
    assertEquals("s = {\n"
               + "    tmp0 = i .. k;\n"
               + "    r in tmp0 :: 3.0 10..12\n"
               + "  @ r\n"
               + "  }",
        set.toString());
  }

  public void testFreeVars()
  {
    Set<ZName> vars = set.freeVars();
    Assert.assertEquals(3, vars.size());
    Assert.assertTrue(vars.contains(i));
    Assert.assertTrue(vars.contains(k));
    Assert.assertTrue(vars.contains(s));
  }
}




