/*
  Copyright 2003, 2004, 2006, 2007 Mark Utting
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

package net.sourceforge.czt.z.impl;

import junit.framework.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

/**
 * A (junit) test class which contains a collection of AST tests
 * like calling create methods, validating, etc.
 *
 * @author Petra Malik
 */
public class AstTest extends TestCase
{
  public static Test suite()
  {
    TestSuite suite = new TestSuite();

    suite.addTestSuite(AndExprTest.class);
    suite.addTestSuite(OrExprTest.class);
    suite.addTestSuite(OptempParaTest.class);

    return suite;
  }

  /**
   * A (junit) test class for AndExpr.
   */
  public static class AndExprTest
    extends TermTest
  {
    private Factory factory_ = new Factory();

    public AndExprTest(String name)
    {
      super(name);
    }

    protected Term createTerm()
    {
      return factory_.createAndExpr();
    }
  }

  /**
   * A (junit) test class for OrExpr.
   */
  public static class OrExprTest
    extends TermTest
  {
    private Factory factory_ = new Factory();

    public OrExprTest(String name)
    {
      super(name);
    }

    protected Term createTerm()
    {
      return factory_.createOrExpr(factory_.createOrExpr(),
                                   factory_.createOrExpr());
    }
  }

  /**
   * A (junit) test class for OptempPara.
   */
  public static class OptempParaTest
    extends TermTest
  {
    private Factory factory_ = new Factory();

    public OptempParaTest(String name)
    {
      super(name);
    }

    protected Term createTerm()
    {
      return factory_.createOptempPara();
    }

    public void testInsertWord()
    {
      OptempPara optempPara = factory_.createOptempPara();
      Operator op1 = factory_.createOperator("Test1");
      Operand op2 = factory_.createOperand();
      optempPara.getOper().add(op1);
      Assert.assertEquals(optempPara.getOper().get(0), op1);
      optempPara.getOper().add(op2);
      Assert.assertEquals(optempPara.getOper().get(1), op2);
    }
  }
}
