/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/

package net.sourceforge.czt.animation.eval;

import java.util.Iterator;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Spec;

public class ZLiveTest extends ZTestCase
{
  String spec = "\\begin{zsection} \\SECTION eg1 \\parents standard\\_toolkit \\end{zsection}\n"
    + "A simple Z specification for testing ZLive schema evaluation.\n"
    + "\\begin{schema}{State}\n"
    + "  a,b : 0 \\upto 10\n"
    + "  \\where\n"
    + "  a < b\n"
    + "\\end{schema}\n"
    + "\\begin{schema}{Init}\n"
    + "  a', b' : 0 \\upto 10\n"
    + "\\where\n"
    + "    a' = 0 \\land b' = 10\n"
    + "\\end{schema}\n"
    + "\n"
    + "\\begin{schema}{AIncr}\n"
    + "    a : 0 \\upto 10 \\\\ \n"
    + "    b : 0 \\upto 10 \\\\ \n"
    + "    a' : 0 \\upto 10 \\\\ \n"
    + "    b' : 0 \\upto 10 \\\\ \n"
    + "\\where\n"
    + "    b' = b \\\\ \n"
    + "    a' = a + 1\n"
    + "\\end{schema}\n"
    + "\n"
    + "This operation is non-deterministic.\n"
    + "It increases a by any amount, so long as it stays less than b.\n"
    + "\n"
    + "\\begin{schema}{ALarger}\n"
    + "    a, b, a', b' : 0 \\upto 10\n"
    + "\\where\n"
    + "    b' = b \\\\ \n"
    + "    a' > a\n"
    + "\\end{schema}";

  public void setUp()
  throws CommandException
  {
    Source src = new StringSource(spec);
    src.setMarkup(Markup.LATEX);
    Key key = new Key("eg1", Source.class);
    zlive_.getSectionManager().put(key, src);
    zlive_.setCurrentSection("eg1");
  }

  public void testEg1()
  throws CommandException
  {
    assertEquals("eg1", zlive_.getCurrentSection());
    Key key = new Key("eg1", Spec.class);
    assertNotNull(zlive_.getSectionManager().get(key));
  }

  public void testEvalExpr()
  {
    Expr input = parseExpr("1+2");
    Expr result = zlive_.evalExpr(input);
    Expr expected = parseExpr("3");
    Assert.assertEquals(expected, result);
  }

  public void testEvalPred()
  {
    Pred input = parsePred("1<2");
    Pred result = zlive_.evalPred(input);
    Pred expected = parsePred("true");
    Assert.assertEquals(expected, result);
  }

  /** This tests the evaluation of schema AIncr with a==0 and b==10. */
  public void testEvalOperation1()
  throws CommandException
  {
    BindExpr args = (BindExpr) parseExpr("\\lblot a==0, b==10 \\rblot");
    //ZFormatter.startLogging("net.sourceforge.czt.animation.eval",
    //    "evalSchema.log", Level.FINEST);
    EvalSet set = zlive_.evalSchema("AIncr", args);
    Assert.assertEquals(1, set.size());
    Iterator<Expr> iter = set.iterator();
    assertTrue(iter.hasNext());
    BindExpr expect = (BindExpr) parseExpr("\\lblot a'==1, b'==10 \\rblot");
    assertTrue(ExprComparator.equalZ(expect, iter.next()));
    //ZFormatter.stopLogging("net.sourceforge.czt.animation.eval");
  }

  public void testReset()
  {
    zlive_.reset();
    Assert.assertEquals("ZLiveDefault", zlive_.getCurrentSection());
    Key key = new Key("eg1", Spec.class);
    try {
      Object result = zlive_.getSectionManager().get(key);
      Assert.fail("section manager should be empty, but eg1="+result);
    }
    catch (CommandException ex) {
      // good!  We should get this exception.
    }
  }


  public void testVersionNumberPresent()
  {
    String version = ZLive.getVersion();
    assertTrue(version.startsWith("0") || version.startsWith("1"));
  }
}
