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
package net.sourceforge.czt.animation.eval.flatpred;

import java.io.*;
import java.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.print.z.PrintUtils;


/** Manages a list of FlatPred predicates.
 *  Provides methods for adding declarations and predicates
 *  to the list, doing mode analysis of the list, and
 *  evaluating the list (giving a series of updated environments).
 */
public class FlatPredList
{
  /** Creates an empty FlatPred list. */
  public FlatPredList() {
  }
  
  public int size()
  { return predlist_.size(); }
  
  public Iterator iterator()
  { return predlist_.iterator(); }
  
  /** Adds one declaration to the FlatPred list.
   *  This converts x,y:T into x \in T \land y \in T.
   *  (More precisely, into: tmp=T; x \in tmp; y \in tmp).
   * 
   * @param decl  May declare several variables.
   */
  public void addDecl(/*@non_null@*/Decl decl) {
    if (decl instanceof VarDecl) {
      VarDecl vdecl = (VarDecl)decl;
      Expr type = vdecl.getExpr();
      RefName typeName = flattener.flattenExpr(type,predlist_);
      Iterator i = vdecl.getDeclName().iterator();
      while (i.hasNext()) {
        DeclName var = (DeclName)i.next();
        RefName varref = factory_.createRefName(var);
        declared_.add(varref);
        predlist_.add(new FlatMember(typeName,varref));
      }
    } else if (decl instanceof ConstDecl) {
      ConstDecl cdecl = (ConstDecl)decl;
      DeclName var = cdecl.getDeclName();
      Expr expr = cdecl.getExpr();
      RefName varref = factory_.createRefName(var);
      declared_.add(varref);
      flattener.flattenPred(factory_.createMemPred(varref,expr), predlist_);
    } else {
      throw new EvalException("Unknown kind of Decl: "+decl);      
    }
  }

  /** Adds one predicate to the FlatPred list.
   * 
   * @param pred  The Pred to flatten and add.
   */
  public void addPred(/*@non_null@*/Pred pred) {
    flattener.flattenPred(pred,predlist_);
  }

  /** Optimises the list and chooses a mode.
   *  @czt.todo Implement a simple reordering algorithm here.
   *  The current implement does no reordering.
   */
  public Mode chooseMode(Envir env0) {
    Envir env = env0;
    double cost = 1.0;
    Iterator i = predlist_.iterator();
    while (i.hasNext()) {
      FlatPred fp = (FlatPred)i.next();
      Mode m = fp.chooseMode(env);
      if (m == null)
        return null;
      fp.setMode(m);
      env = m.getEnvir();
      cost *= m.getSolutions();
    }
    return new Mode(env, empty_, cost);
  }

  /** Starts a fresh evaluation.
   */
  public void startEvaluation(/*@non_null@*/Mode mode, Envir env0)
  {
    evalMode_ = mode;
    inputEnv_ = env0;
    outputEnv_ = mode.getEnvir();
    solutionsReturned = 0;
  }

  /** The output environment of this FlatPred list.
   *  This is only valid after startEvaluation.
   */
  public Envir getOutputEnvir() {
    return outputEnv_;
  }
  
  /** Returns the next solution from this list of FlatPreds.
   *  This implements chronological backtracking, like Prolog.
   *  If it returns true, the output environment has been updated.
   *  @return true iff a new solution was found.
   */
  public boolean nextEvaluation() {
    final int end = predlist_.size();
    int curr = end - 1;
    if (solutionsReturned == 0) {
      curr = 0;  // start from the beginning!
      ((FlatPred)predlist_.get(curr)).startEvaluation();
    }
    solutionsReturned++;
    while (0 <= curr && curr < end) {
      FlatPred fp = (FlatPred)predlist_.get(curr);
      if (fp.nextEvaluation()) {
        curr++;
         if (curr < end)
          ((FlatPred)predlist_.get(curr)).startEvaluation();
      }
      else {
        curr--;
     }
    }
    return curr == end;
  }

  /** Prints the list of FlatPreds used in the last call
    * to evalPred or evalExpr.
    */
  public void printCode()
  {
    try {
      System.out.println("Printing " + predlist_.size() + " preds:");
      writer.write("Start of the Loop\n");
      for (Iterator i = predlist_.iterator(); i.hasNext(); ) {
        FlatPred p = (FlatPred) i.next();
        writer.write("Print flat " + p.toString() + "\n");
        //print(p, writer);
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
  
  /**
  private void print(Term t, Writer writer) throws IOException
  {
    ZLiveToAstVisitor toAst = new ZLiveToAstVisitor();
    Term ast = (Term) t.accept(toAst);
    //writer.write(ast);
    PrintUtils.printUnicode(ast, writer, sectman_);
    writer.write("\n");
  }
  */

  /** This stores the list of FlatPreds used in the current evaluation. */
  protected List predlist_ = new ArrayList();
  
  /** Records the bound variables in this list.
   *  (Ignoring the tmp vars produced by Flatten).
   */
  protected Set/*<RefName>*/ declared_ = new HashSet();

  /** Used to flatten a predicate into a list of FlatPreds. */
  static Flatten flattener = new Flatten();
  
  protected Factory factory_ = new Factory();
  
  /** A Writer interface to System.out. */
  protected Writer writer = new BufferedWriter(new OutputStreamWriter(System.out));

  private static ArrayList empty_ = new ArrayList();
  
  private Mode evalMode_;
  private Envir inputEnv_;
  private Envir outputEnv_;
  
  /** The number of solutions that have been returned by nextEvaluation().
  This is -1 before startEvaluation() is called and 0 immediately
  after it has been called.
  */
  protected int solutionsReturned = -1;
}
