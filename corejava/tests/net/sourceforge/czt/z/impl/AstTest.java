/**
Copyright 2003 Mark Utting
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
import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.JaxbValidator;

/**
 * A (junit) test class which contains some AST tests.
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

  public static class AndExprTest
    extends TermATest
  {
    private ZFactory zFactory_ = new ZFactoryImpl();

    public AndExprTest(String name)
    {
      super(name);
    }

    protected TermA createTermA()
    {
      return zFactory_.createAndExpr();
    }
  }

  public static class OrExprTest
    extends TermATest
  {
    private ZFactory zFactory_ = new ZFactoryImpl();

    public OrExprTest(String name)
    {
      super(name);
    }

    protected TermA createTermA()
    {
      return zFactory_.createOrExpr(zFactory_.createOrExpr(),
                                    zFactory_.createOrExpr());
    }
  }

  public static class OptempParaTest
    extends TermATest
  {
    private ZFactory zFactory_ = new ZFactoryImpl();

    public OptempParaTest(String name)
    {
      super(name);
    }

    protected TermA createTermA()
    {
      return zFactory_.createOptempPara();
    }

    public void testInsertWord()
    {
      OptempPara optempPara = zFactory_.createOptempPara();
      Operator op1 = zFactory_.createOperator("Test1");
      Operand op2 = zFactory_.createOperand();
      optempPara.getOper().add(op1);
      Assert.assertEquals(optempPara.getOper().get(0), op1);
      optempPara.getOper().add(op2);
      Assert.assertEquals(optempPara.getOper().get(1), op2);
    }

    public void testValidation()
    {
      OptempPara optempPara = zFactory_.createOptempPara();
      Operator op1 = zFactory_.createOperator("Test1");
      Operand op2 = zFactory_.createOperand();
      optempPara.getOper().add(op1);
      optempPara.getOper().add(op2);
      optempPara.setCat(Cat.Relation);
      optempPara.setPrec(new Integer(12));
      AstValidator validator = new JaxbValidator();
      Assert.assertTrue(validator.validate(optempPara));
    }
  }
}
