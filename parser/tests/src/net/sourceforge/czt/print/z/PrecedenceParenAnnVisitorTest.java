/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.print.z;

import junit.framework.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

/**
 * A (JUnit) test class for testing the PrecedenceParenAnnVisitor.
 *
 * @author Petra Malik
 */
public class PrecedenceParenAnnVisitorTest
  extends TestCase
{
  Factory factory_ = new Factory();
  SectionManager manager_ = new SectionManager();

  public void testApplExpr()
  {
    PrecedenceParenAnnVisitor visitor =
      new PrecedenceParenAnnVisitor(manager_);
    setOperatorTable(visitor);
    RefName n = factory_.createRefName("n");
    RefName neg = factory_.createRefName(" - _ ");
    RefName iter = factory_.createRefName("iter");
    ApplExpr funApp =
      factory_.createFunOpAppl(neg, factory_.createRefExpr(n));
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor();
    Term tree = (Term) funApp.accept(toPrintTree);
    Assert.assertTrue(visitor.isFunOrGenOpAppl(tree) != null);
    Assert.assertTrue(visitor.isPrefix(visitor.isFunOrGenOpAppl(tree)));
    Assert.assertEquals(visitor.precedence(tree), 190.0, 0);

    ApplExpr appl = factory_.createApplication(iter, funApp);
    tree = (Term) appl.accept(toPrintTree);
    tree.accept(visitor);
    Application application = (Application) tree;
    Expr rightExpr = application.getRightExpr();
    Assert.assertTrue(rightExpr.getAnn(ParenAnn.class) != null);
  }

  public void testAssoc()
  {
    RefExpr a = factory_.createRefExpr(factory_.createRefName("a"));
    RefExpr b = factory_.createRefExpr(factory_.createRefName("b"));
    RefExpr c = factory_.createRefExpr(factory_.createRefName("c"));
    RefName plus = factory_.createRefName(" _ + _ ");
    Expr plus1 =
      factory_.createFunOpAppl(plus, factory_.createTupleExpr(b, c));
    Expr plus2 =
      factory_.createFunOpAppl(plus, factory_.createTupleExpr(a, plus1));
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor();
    Term tree = (Term) plus2.accept(toPrintTree);
    PrecedenceParenAnnVisitor visitor =
      new PrecedenceParenAnnVisitor(manager_);
    setOperatorTable(visitor);
    tree.accept(visitor);
    TermA secondArg = (TermA) tree.getChildren()[1];
    Assert.assertTrue(secondArg.getAnn(ParenAnn.class) != null);
  }

  /**
   * Sets the operator table of the given visitor to standard_toolkit.
   */
  private void setOperatorTable(Visitor visitor)
  {
    ZSect zSect =
      factory_.createZSect("standard_toolkit", null, null);
    zSect.accept(visitor);
  }
}
