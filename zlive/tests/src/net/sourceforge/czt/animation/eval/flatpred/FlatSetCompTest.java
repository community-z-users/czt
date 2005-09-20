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

import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.math.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;


/**
 * A (JUnit) test class for testing the FlatSetComp class.
 *
 * @author Mark Utting
 */
public class FlatSetCompTest
  extends FlatRangeSetTest
{
  /** This overrides set and emptySet to be FlatDiscreteSet objects.
   *  set = {i,k,j,i} and emptySet = {}.
   */
  String setCompStr = "\\{ r : i \\upto k @ r \\}";
  String emptySetCompStr = "\\{ r : k \\upto i | r \\in \\{9\\} @ r \\}";
  ZLive zlive = new ZLive();

  public FlatSetCompTest()
  {
    SetCompExpr setComp = null;
    SetCompExpr emptySetComp = null;
    try {
      Source e = new StringSource(setCompStr);
      e.setMarkup(Markup.LATEX);
      setComp = (SetCompExpr)ParseUtils.parseExpr(e, null,
						  zlive.getSectionManager());
      e = new StringSource(emptySetCompStr);
      e.setMarkup(Markup.LATEX);
      emptySetComp = (SetCompExpr)ParseUtils.parseExpr(e, null,
						  zlive.getSectionManager());
    } catch (Exception e) {
      fail("Error parsing set expr: " + e);
    }
    ZSchText text = setComp.getZSchText();
    set = new FlatSetComp(zlive,
			  text.getDecl(),
			  text.getPred(),
			  setComp.getExpr(),
			  s);
    text = emptySetComp.getZSchText();
    emptySet = new FlatSetComp(zlive,
			       text.getDecl(),
			       text.getPred(),
			       emptySetComp.getExpr(),
			       s);
  }

  public void testFreeVars()
  {
    Set vars = set.freeVars();
    Assert.assertEquals(vars.size(), 2);
    Assert.assertTrue(vars.contains(i));
    Assert.assertFalse(vars.contains(j));
    Assert.assertTrue(vars.contains(k));
  }
}




