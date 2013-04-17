/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.util.Section;
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
  SectionManager manager_ = new SectionManager(Dialect.Z);

  public void testApplExpr()
  {
    try {
      final OpTable standardToolkitOpTable =
        manager_.get(new Key<OpTable>(Section.STANDARD_TOOLKIT.getName(), OpTable.class));
      PrecedenceParenAnnVisitor visitor =
        new PrecedenceParenAnnVisitor();
      setOperatorTable(visitor);
      ZName n = factory_.createZName("n");
      ZName neg = factory_.createZName(" - _ ");
      ZName iter = factory_.createZName("iter");
      ApplExpr funApp =
        factory_.createFunOpAppl(neg, factory_.createRefExpr(n));
      AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager_);
      Term tree = toPrintTree.run(funApp, standardToolkitOpTable);
      final int prec = 190;
      Assert.assertEquals(visitor.precedence(tree),
                          Precedence.precedence(prec));
      ApplExpr appl = factory_.createApplication(iter, funApp);
      tree = (Term) appl.accept(toPrintTree);
      tree.accept(visitor);
      Application application = (Application) tree;
      Expr rightExpr = application.getRightExpr();
      Assert.assertTrue(rightExpr.getAnn(ParenAnn.class) != null);
    }
    catch (CommandException exception) {
      fail("Should not throw CommandException " + exception);
    }
  }

  public void testAssoc()
  {
    try {
      final OpTable standardToolkitOpTable =
        manager_.get(new Key<OpTable>(Section.STANDARD_TOOLKIT.getName(), OpTable.class));
      RefExpr a = factory_.createRefExpr(factory_.createZName("a"));
      RefExpr b = factory_.createRefExpr(factory_.createZName("b"));
      RefExpr c = factory_.createRefExpr(factory_.createZName("c"));
      Name plus = factory_.createZName(" _ + _ ");
      Expr plus1 =
        factory_.createFunOpAppl(plus, factory_.createTupleExpr(b, c));
      Expr plus2 =
        factory_.createFunOpAppl(plus, factory_.createTupleExpr(a, plus1));
      AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager_);
      Term tree = (Term) toPrintTree.run(plus2, standardToolkitOpTable);
      PrecedenceParenAnnVisitor visitor =
        new PrecedenceParenAnnVisitor();
      setOperatorTable(visitor);
      tree.accept(visitor);
      Term secondArg = (Term) tree.getChildren()[1];
      Assert.assertTrue(secondArg.getAnn(ParenAnn.class) != null);
    }
    catch (CommandException exception) {
      fail("Should not throw CommandException " + exception);
    }
  }

  /**
   * Sets the operator table of the given visitor to standard_toolkit.
   */
  private void setOperatorTable(Visitor<?> visitor)
  {
    ZSect zSect =
      factory_.createZSect("standard_toolkit", null, null);
    zSect.accept(visitor);
  }
}
