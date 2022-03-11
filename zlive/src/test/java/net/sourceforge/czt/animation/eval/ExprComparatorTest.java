/**
Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.animation.eval;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import net.sourceforge.czt.z.ast.Expr;

public class ExprComparatorTest extends ZTestCase
{
  /** A vector of expressions to compare */
  private List<Expr> exprs;

  /** A total ordering of the expressions in exprs. */
  private List<Integer> positions;

  private ExprComparator sut;

  protected void setUp() throws Exception
  {
    super.setUp();
    sut = ExprComparator.create();
  }

  protected void setUpExprs() throws Exception
  {
    exprs = new ArrayList<Expr>();
    positions = new ArrayList<Integer>();
    exprs.add(parseExpr("0"));  positions.add(0);
    exprs.add(parseExpr("1000000000000"));  positions.add(2);

    // TODO: define some free types and order their instances.

    // tuples (ordered by arity, then left to right)
    exprs.add(parseExpr("(1,1)"));  positions.add(411);
    exprs.add(parseExpr("(1,2)"));  positions.add(412);
    exprs.add(parseExpr("(2,1)"));  positions.add(421);
    exprs.add(parseExpr("(1,1,1)"));  positions.add(423);

    // bindings (ordered by number of entries, then the sorted names, then the values)
    exprs.add(parseExpr("\\lblot \\rblot"));  positions.add(500);
    exprs.add(parseExpr("\\lblot a==1 \\rblot"));  positions.add(511);
    exprs.add(parseExpr("\\lblot a==2 \\rblot"));  positions.add(512);
    exprs.add(parseExpr("\\lblot a==1, b==3, c==5 \\rblot"));  positions.add(523);
    exprs.add(parseExpr("\\lblot             c==5, b==3, a==1 \\rblot"));  positions.add(523);
    exprs.add(parseExpr("\\lblot a==1, b==3, c==6 \\rblot"));  positions.add(524);
    exprs.add(parseExpr("\\lblot a==1, b==4, c==1 \\rblot"));  positions.add(525);
    exprs.add(parseExpr("\\lblot a==2, b==1, c==1 \\rblot"));  positions.add(526);
    exprs.add(parseExpr("\\lblot a==2, b'==1, c?==1 \\rblot"));  positions.add(527);

    // sets (ordered by size, then lexigraphically on sorted members)
    addset("3 \\upto 1");  positions.add(600);
    addset("\\{ x:0 \\upto 10 | x > 20 \\}");  positions.add(600);
    addset("1 \\upto 3");  positions.add(601);
    addset("\\{ 1, 3, 5 \\}");  positions.add(602);
    addset("\\{ 5, 3, 1, 3 \\}");  positions.add(602);
    addset("\\{ x:1 \\upto 5 | x \\mod 2 = 1 \\}");  positions.add(602);
    addset("\\{ 1, 3, 6 \\}");  positions.add(603);
    addset("\\{ 1, 4, 5 \\}");  positions.add(604);
    addset("\\{ 2, 3, 5 \\}");  positions.add(605);
    addset("(2 \\upto 3) \\cup \\{ 5 \\}");  positions.add(605);
  }

  protected void addset(String set)
  {
    Expr e = parseExpr(set);
    exprs.add(zlive_.evalExpr(e));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.eval.ExprComparator.compare(Expr, Expr)'
   */
  public void testCompare() throws Exception
  {
    setUpExprs();
    // exhaustive testing of all pairs in exprs list.
    for (int i=0; i<exprs.size(); i++)
      for (int j=i; j<exprs.size(); j++) {
        int expect = positions.get(i).compareTo(positions.get(j));
        int actual = sut.compare(exprs.get(i), exprs.get(j));
        Assert.assertEquals("compare("+i+","+j+") with positions="
            +positions.get(i)+","+positions.get(j),
            expect, actual);
      }
  }

  public void testSign()
  {
    Assert.assertEquals(-1, sut.sign(-111));
    Assert.assertEquals(-1, sut.sign(-1));
    Assert.assertEquals(0, sut.sign(0));
    Assert.assertEquals(1, sut.sign(1));
    Assert.assertEquals(1, sut.sign(111));
  }
}
