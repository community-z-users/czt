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

import java.io.*;
import java.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.print.z.PrintUtils;

public class ZLive
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  //Factory();
  
  /** A Writer interface to System.out. */
  protected Writer writer = new BufferedWriter(new OutputStreamWriter(System.out));

  protected SectionManager sectman_ = new SectionManager();

  /** This stores the list of FlatPreds used in the current evaluation. */
  protected List preds_ = new ArrayList();
  
   /**
   * Returns the factory used for creating AST objects.
   */
  public ZFactory getFactory()
  {
    return factory_;
  }

  /**
   * Sets the AST factory used for creating AST objects.
   **/
  public void setFactory(ZFactory zFactory)
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
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
    preds_.clear();
    Envir env = new Envir();
    flattener.flatten(pred, preds_);
    // We assume left to right evaluation will work.
    // TODO: implement A* algorithm here.
    for (Iterator i = preds_.iterator(); i.hasNext(); ) {
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
    for (Iterator i = preds_.iterator(); i.hasNext(); ) {
      FlatPred p = (FlatPred)i.next();
      p.startEvaluation();
      if (!p.nextEvaluation())  // TODO: loop through all solutions.
        return factory_.createFalsePred();
    }
    return factory_.createTruePred();
  }

  /** Prints the list of FlatPreds used in the last call
    * to evalPred or evalExpr.
    */
  public void printCode()
  {
    try {
      System.out.println("Printing " + preds_.size() + " preds:");
      writer.write("Start of the Loop\n");
      for (Iterator i = preds_.iterator(); i.hasNext(); ) {
        FlatPred p = (FlatPred) i.next();
        writer.write("Print flat " + p.toString() + "\n");
        print(p, writer);
        //writer.write("Printed flat " + p.toString() + "\n");
      }
      writer.write("End of the loop\n");
      writer.flush();
      //writer.close();
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    System.out.println("END");
  }
  
  private void print(Term t, Writer writer) throws IOException
  {
    ZLiveToAstVisitor toAst = new ZLiveToAstVisitor();
    Term ast = (Term) t.accept(toAst);
    //writer.write(ast);
    PrintUtils.printUnicode(ast, writer, sectman_);
    writer.write("\n");
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
