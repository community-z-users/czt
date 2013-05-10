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

package net.sourceforge.czt.rules.unification;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.Joker;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.ast.ProverJokerExpr;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.zpatt.ast.Binding;
import net.sourceforge.czt.zpatt.ast.JokerExpr;
import net.sourceforge.czt.zpatt.util.Factory;

public class UnifierTest extends TestCase
{
  /** A vector of expressions to compare */
  private List<Expr> exprs;

  /** A string representation of the expected result */
  private List<String> positions;

  private SectionManager sectman_ = new SectionManager(Dialect.ZPATT);

  /** Convenience method for creating expressions for testing.
   *  It uses the ZPattern parser, so that it can parse jokers.
   */
  public Expr zpattExpr(String str)
  throws IOException, CommandException
  {
    Expr expr = UnificationUtils.parseExpr(str, null, sectman_);
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor copyVisitor = new CopyVisitor(factory);
    return (Expr) expr.accept(copyVisitor);
  }

  @Override
  protected void setUp() throws Exception
  {
    super.setUp();

    exprs = new ArrayList<Expr>();
    positions = new ArrayList<String>();
    exprs.add(zpattExpr("0"));            positions.add("num0");
    exprs.add(zpattExpr("10000000000"));  positions.add("num1"); // > MAXINT

    // tuples
    exprs.add(zpattExpr("(1, 1, 1)"));  positions.add("(1,1,1)");
    exprs.add(zpattExpr("(1, 2, 1)"));  positions.add("(1,2,1)");
    exprs.add(zpattExpr("(E1,2, 1)"));  positions.add("(1,2,1)");   // must be 4th one.
    exprs.add(zpattExpr("(1, 2,E2)"));  positions.add("(1,2,1)");

    // set comprehensions, with decllist jokers and pred jokers.
    exprs.add(zpattExpr("\\{x:E1;D1|x<3\\}"));        positions.add("set_x");
    exprs.add(zpattExpr("\\{x:E1|x<3\\}"));           positions.add("set_x|x3");
    exprs.add(zpattExpr("\\{x:E1;y:E2|x<3\\}"));      positions.add("set_x_y|x3");
    exprs.add(zpattExpr("\\{x:\\nat;y:\\nat|P2\\}")); positions.add("set_x_y|");

    // check that instantiated generics unify with non-instantiated generics.
    exprs.add(zpattExpr("x"));                positions.add("ref_x_");
    exprs.add(zpattExpr("x[\\nat]"));         positions.add("ref_x_nat");
    exprs.add(zpattExpr("x[\\power \\nat]")); positions.add("ref_x_powernat");
    exprs.add(zpattExpr("y[\\nat]"));         positions.add("ref_y_nat");
  }

  /** Tests that jokers like E1 are being parsed correctly. */
  public void testJoker()
  {
    Expr e = exprs.get(4);
    assertTrue(e instanceof TupleExpr);
    TupleExpr tuple = (TupleExpr)e;
    assertTrue(tuple.getZExprList().size() == 3);
    Expr joker = tuple.getZExprList().get(0);
    //    System.out.println("E1 was parsed as a joker: "+joker);
    assertTrue(joker instanceof Joker);
    assertTrue(joker instanceof JokerExpr);
    assertTrue(joker instanceof ProverJokerExpr);
  }

  /*
   * Test method for 'net.sourceforge.czt.rules.unification.Unifier'
   * and 'net.sourceforge.czt.rules.unification.UnificationUtils'
   */
  public void testUnify()
  {
    // exhaustive testing of all pairs in exprs list.
    for (int i=0; i<exprs.size(); i++)
      for (int j=0; j<exprs.size(); j++) {
        String msg = "unify("+i+","+j+") with positions="
          +positions.get(i)+","+positions.get(j);
        Set<Binding> result = UnificationUtils.unify(exprs.get(i), exprs.get(j));
        //        System.out.println(msg+" gives "+result);
        if (positions.get(i).startsWith(positions.get(j))
            || positions.get(j).startsWith(positions.get(i))) {
          assertNotNull(msg, result);
          // now undo any bindings made by unify.
          for (Binding bind : result)
            bind.reset();
        }
        else
          assertNull(msg, result);
      }
  }
}
