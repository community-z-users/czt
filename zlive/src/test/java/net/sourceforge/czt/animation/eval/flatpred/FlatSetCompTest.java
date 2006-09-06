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
import net.sourceforge.czt.z.ast.ZSchText;


/**
 * A (JUnit) test class for testing the FlatSetComp class.
 *
 * @author Mark Utting
 */
public class FlatSetCompTest
  extends EvalSetTest
{
  /** This overrides set and emptySet to be FlatDiscreteSet objects.
   *  set = {i,k,j,i} and emptySet = {}.
   */
  String setCompStr = "\\{ r : i \\upto k @ r \\}";
  String emptySetCompStr = "\\{ r : k \\upto i | r \\in \\{9\\} @ r \\}";

  public FlatSetCompTest()
  {
  }

  public void setUp()
  {
    SetCompExpr setComp = (SetCompExpr) parseExpr(setCompStr);
    SetCompExpr emptySetComp = (SetCompExpr) parseExpr(emptySetCompStr);
    ZSchText text = setComp.getZSchText();
    set = new FlatPredList(zlive_);
    set.add(new FlatSetComp(zlive_,
			  text.getZDeclList(),
			  text.getPred(),
			  setComp.getExpr(),
			  s));
    set.inferBounds(new Bounds());

    emptySet = new FlatPredList(zlive_);
    text = emptySetComp.getZSchText();
    emptySet.add(new FlatSetComp(zlive_,
			       text.getZDeclList(),
			       text.getPred(),
			       emptySetComp.getExpr(),
			       s));
    emptySet.inferBounds(new Bounds());
  }

  public void testFreeVars()
  {
    Set vars = set.freeVars();
    Assert.assertEquals(3, vars.size());
    Assert.assertTrue(vars.contains(i));
    Assert.assertFalse(vars.contains(j));
    Assert.assertTrue(vars.contains(k));
    Assert.assertTrue(vars.contains(s));
  }
}




