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

import java.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

public class ZLive
{
  private Factory factory_ = new Factory();
  
  protected SectionManager sectman_ = new SectionManager();

  /**
   * Returns the factory used for creating AST objects.
   */
  public Factory getFactory()
  {
    return factory_;
  }

  /**
   * Sets the AST factory used for creating AST objects.
   **/
  public void setFactory(ZFactory zFactory)
  {
    factory_ = new Factory(zFactory);
  }

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
    Flatten flattener = new Flatten();
    List preds = new ArrayList();
    Envir env = new Envir();
    flattener.flatten(pred, preds);
    if (preds.size() == 0)
      throw new EvalException("Flatten not working yet");
    // We assume left to right evaluation will work.
    // TODO: implement A* algorithm here.
    for (Iterator i = preds.iterator(); i.hasNext(); ) {
      FlatPred p = (FlatPred)i.next();
      Mode m = p.chooseMode(env);
      if (m == null)
        throw new EvalException("Cannot find mode");
      else {
        p.setMode(m);
        env = m.getEnvir();
      }
    }
    // Execute the list of predicates.
    for (Iterator i = preds.iterator(); i.hasNext(); ) {
      FlatPred p = (FlatPred)i.next();
      p.startEvaluation();
      if (!p.nextEvaluation())  // TODO: loop through all solutions.
        return factory_.createFalsePred();
    }
    return factory_.createTruePred();
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
