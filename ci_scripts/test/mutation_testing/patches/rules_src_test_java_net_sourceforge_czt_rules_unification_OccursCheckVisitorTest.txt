/*
  Copyright (C) 2006, 2007 Mark Utting
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.ast.ProverJokerExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.MemPred;
import junit.framework.TestCase;

public class OccursCheckVisitorTest extends TestCase
{
  private OccursCheckVisitor occursCheck_;
  private String jokerName_ = "testJoker";
  private ProverJokerExpr joker_;
  private ProverFactory factory_;
  
  protected void setUp() throws Exception
  {
    super.setUp();
    occursCheck_ = new OccursCheckVisitor();
    factory_ = new ProverFactory();
    joker_ = (ProverJokerExpr) factory_.createJokerExpr(jokerName_, null);
    
  }

  public void testContains1()
  {
    assertTrue(occursCheck_.contains(joker_, joker_));
  }
  
  public void testContains2()
  {
    Term ground = factory_.createNextStroke();
    assertFalse(occursCheck_.contains(ground, joker_));
  }
  
  public void testContains3()
  {
    Expr right = factory_.createSetExpr();
    MemPred pred = factory_.createMemPred();
    pred.setLeftExpr(joker_);
    pred.setRightExpr(right);
    pred.setMixfix(Boolean.TRUE);
    assertTrue(occursCheck_.contains(pred, joker_));
  }
  
  public void testContains4()
  {
    Expr left = factory_.createSetExpr();
    Expr joker2 = factory_.createJokerExpr("otherJoker", null);
    MemPred pred = factory_.createMemPred();
    pred.setLeftExpr(left);
    pred.setRightExpr(joker2);
    pred.setMixfix(Boolean.TRUE);
    assertFalse(occursCheck_.contains(pred, joker_));
  }
  
  /** Check that multiple instances of the same name joker are equal. */
  public void testContains5()
  {
    Expr left = factory_.createSetExpr();
    Expr samejoker = factory_.createJokerExpr("jokerName_", null);
    MemPred pred = factory_.createMemPred();
    pred.setLeftExpr(left);
    pred.setRightExpr(samejoker);
    pred.setMixfix(Boolean.TRUE);
    assertFalse(occursCheck_.contains(pred, joker_));
  }
}
