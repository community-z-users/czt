/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.animation.eval.*;

public class ZLive
{
  /** @czt.todo Allow this factory to be customised. */
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  
  protected SectionManager sectman_ = new SectionManager();

  /** Get the current section manager. */
  public SectionManager getSectionManager()
  { return sectman_; }

  /** Set the section manager which will be used during evaluation. */
  //@ requires sm != null;
  public void setSectionManager(SectionManager sm)
  { sectman_ = sm; }

  /** Which section evaluations are being done in. */
  public String getCurrentSection()
  { return "Specification"; }

  /** Say which section future evaluations will be done in. */
  public void setCurrentSection(String sectname)
  {}

  /** Evaluate a Pred.
      This throws some kind of EvalException if pred is too difficult
      to evaluate or contains an undefined expression.
      @param pred  A net.sourceforge.czt.z.ast.Pred object.
      @return      Usually an instance of TruePred or FalsePred.
  */
  public Pred evalPred(Pred pred)
    throws EvalException
  {
	  return factory_.createTruePred();
    // throw new EvalException("Not implemented yet: " + pred);
  }

  /** Evaluate an Expr.
      This throws some kind of EvalException if expr is too difficult
      to evaluate or contains an undefined expression.
      @param expr  A net.sourceforge.czt.z.ast.Pred object.
      @return      Usually an instance of EvalSet, or some other expr.
  */
  public Expr evalExpr(Expr expr)
    throws EvalException
  {
	//  return expr;
    throw new EvalException("Not implemented yet: " + expr);
  }

  public static void main(String args[])
  {
    System.out.println("ZLive version 0.0");
  }
}
