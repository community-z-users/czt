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
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.CommandException;

/** Manages a list of FlatPred predicates.
 *  Provides methods for adding declarations and predicates
 *  to the list, doing mode analysis of the list, and
 *  evaluating the list (giving a series of updated environments).
 *  <p>
 *  Here is a typical use of FlatPredList:
 *  </p>
 *  <code>
    // Stage 1: Setup.
    predlist = new FlatPredList( ...a Flatten object...);
    ... now add decls, preds, and expressions...
    RefName resultName = predlist.addExpr(expr);
    Envir env0 = new Envir(); // empty environment

    // Stage 2: Optimisation.
    // Ask the FlatPredList to optimise itself for
    // efficient evaluation, given the inputs in env0.
    Mode m = predlist.chooseMode(env0);
    if (m == null)
      throw new EvalException("Cannot find mode to evaluate " + expr);

    // Stage 3: Evaluation.
    predlist.startEvaluation(m,env0);
    while (predlist.nextEvaluation())
        // lookup the result and do something with it.
        System.out.println(predlist.getOutputEnvir().lookup(resultName));
    </code>
 */
public class FlatPredList
{
  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  /** This stores the list of FlatPreds used in the current evaluation. */
  protected List/*<FlatPred>*/ predlist_ = new ArrayList();
  
  /** Records the bound variables in this list.
   *  (Ignoring the tmp vars produced by Flatten).
   *  This is set up as Declarations are added.
   */
  protected /*@non_null@*/ Set/*<DeclName>*/ boundVars_ = new HashSet();

  /** Records the free variables used in this list.
   *  This is calculated and cached by the freeVars() method.
   */
  protected Set/*<RefName>*/ freeVars_;
  
  /** The ZLive animator that owns/uses this FlatPred list. */
  private /*@non_null@*/ ZLive zlive_;
  
  /** Used to flatten a predicate into a list of FlatPreds. */
  /*@non_null@*/ Flatten flatten_;
  
  protected /*@non_null@*/ Factory factory_;
  
  /** A Writer interface to System.out. */
  protected Writer writer = new BufferedWriter(new OutputStreamWriter(System.out));

  private final static ArrayList empty_ = new ArrayList();
  
  private Mode evalMode_;

  /** czt.todo This is not currently used. */
  private Envir inputEnv_;

  private Envir outputEnv_;
  
  /** The number of solutions that have been returned by nextEvaluation().
  This is -1 before startEvaluation() is called and 0 immediately
  after it has been called.
  */
  protected int solutionsReturned = -1;


  /** Creates an empty FlatPred list. */
  public FlatPredList(ZLive newZLive) 
  {
    zlive_ = newZLive;
    flatten_ = new Flatten(newZLive);
    factory_ = zlive_.getFactory();
  }

  /** Returns the number of FlatPreds in this list. */
  public int size()
  { return predlist_.size(); }

  /** An iterator over the FlatPreds in this list.
   *  This should be used as a read-only iterator.
   * @return the iterator
   */
  public /*@non_null@*/ Iterator iterator()
  { return predlist_.iterator(); }

  /** Returns the free variables of all the FlatPreds. */
  public /*@non_null@*/ Set freeVars() {
    if (freeVars_ == null) {
      freeVars_ = new HashSet();
      for (Iterator i = predlist_.iterator(); i.hasNext(); ) {
	FlatPred flat = (FlatPred)i.next();
	for (Iterator v = flat.freeVars().iterator(); v.hasNext(); ) {
	  RefName var = (RefName)v.next();
	  if ( ! zlive_.isNewName(var)) {
	    DeclName dvar = var.getDecl();
	    if (dvar == null)
	      // TODO: this should never happen, because all RefNames
	      // should be linked to a DeclName after typechecking.
	      // For now, we create the corresponding DeclName
	      dvar = factory_.createDeclName(var.getWord(),
					    var.getStroke(),
					    null);
	    if ( ! boundVars_.contains(dvar))
	      freeVars_.add(var);
	  }
	}
      }
    }
    return freeVars_;
  }

  /** Add one FlatPred to the FlatPred list.
   *  This is a low-level method, and addDecl or addPred
   *  should usually be used in preference to this method.
   *  This method should be called before chooseMode is called.
   *
   * @param flat  the FlatPred to add.
   */
  public void add(/*@non_null@*/FlatPred flat) {
    predlist_.add(flat);
  }

  /** Adds a whole schema text to the FlatPred list.
   *  This method should be called before chooseMode is called.
   *
   * @param stext 
   */
  public void addSchText(/*@non_null@*/SchText stext) {
    for (Iterator i = stext.getDecl().iterator(); i.hasNext(); )
      addDecl((Decl)i.next());
    Pred p = stext.getPred();
    if (p != null)
      addPred(p);
  }
  
  /** Adds one declaration to the FlatPred list.
   *  This converts x,y:T into x \in T \land y \in T.
   *  (More precisely, into: tmp=T; x \in tmp; y \in tmp).
   *  This method should be called before chooseMode is called.
   *
   * @param decl  May declare several variables.
   */
  public void addDecl(/*@non_null@*/Decl decl) {
    try {
      if (decl instanceof VarDecl) {
        VarDecl vdecl = (VarDecl) decl;
        Expr type = vdecl.getExpr();
        RefName typeName = flatten_.flattenExpr(type, predlist_);
        Iterator i = vdecl.getDeclName().iterator();
        while (i.hasNext()) {
          DeclName var = (DeclName) i.next();
          boundVars_.add(var);
          RefName varref = factory_.createRefName(var);
          boundVars_.add(varref);
          predlist_.add(new FlatMember(typeName, varref));
        }
      }
      else if (decl instanceof ConstDecl) {
        ConstDecl cdecl = (ConstDecl) decl;
        DeclName var = cdecl.getDeclName();
        boundVars_.add(var);
        Expr expr = cdecl.getExpr();
        RefName varref = factory_.createRefName(var);
        boundVars_.add(varref);
        flatten_.flattenPred(factory_.createMemPred(varref, expr), predlist_);
      }
      else {
        throw new EvalException("Unknown kind of Decl: " + decl);
      }
    }
    catch (CommandException exception) {
      throw new EvalException(exception);
    }
  }

  /** Adds one predicate to the FlatPred list.
   *  This method should be called before chooseMode is called.
   *
   * @param pred  The Pred to flatten and add.
   */
  public void addPred(/*@non_null@*/Pred pred) {
    try {
      flatten_.flattenPred(pred,predlist_);
    }
    catch (CommandException exception) {
      throw new EvalException(exception);
    }
  }

  /** Adds one expression to the FlatPred list.
   *  This method should be called before chooseMode is called.
   *  Returns the 'result' name that will be bound to the result
   *  of the expression after evaluation.  That is,
   *  after chooseMode, startEvaluation and nextEvaluation have
   *  been called, then getOutputEnvir().lookup(result) can
   *  be called to get the value of the evaluated expression.
   *
   * @param expr  The Expr to flatten and add.
   * @return      The result name.
   */
  public RefName addExpr(/*@non_null@*/Expr expr) {
    try {
      return flatten_.flattenExpr(expr,predlist_);
    }
    catch (CommandException exception) {
      throw new EvalException(exception);
    }
  }

  /** Optimises the list and chooses a mode.
   *  @czt.todo Implement a simple reordering algorithm here.
   *  The current implement does no reordering.
   */
  public Mode chooseMode(Envir env0) {
    Envir env = env0;
    double cost = 1.0;
    Iterator i = predlist_.iterator();
    //System.out.println("DEBUG: chooseMode "+this.hashCode());
    while (i.hasNext()) {
      FlatPred fp = (FlatPred)i.next();
      Mode m = fp.chooseMode(env);
      if (m == null) {
        //if (fp instanceof FlatEquals)
          //System.out.println("DEBUG chooseMode "+this.hashCode()+": "+env);
        //System.out.println("DEBUG chooseMode "+this.hashCode()+" returns null because of "+fp+"\n final env="+env);
        return null;
      }
      env = m.getEnvir();
      cost *= m.getSolutions();
      //System.out.println("DEBUG chooseMode "+this.hashCode()+" "+fp+" gives cost="+cost);
    }
    //System.out.println("DEBUG... final cost = "+cost+", final env="+env);
    return new Mode(env, empty_, cost);
  }

  /** Starts a fresh evaluation.
   */
  public void startEvaluation(/*@non_null@*/Mode mode, Envir env0)
  {
    evalMode_ = mode;
    inputEnv_ = env0;
    solutionsReturned = 0;
    // Now set the mode of all the preds in the list.
    double cost = 1.0;
    Iterator i = predlist_.iterator();
    Envir env = env0;
    while (i.hasNext()) {
      FlatPred fp = (FlatPred)i.next();
      Mode m = fp.chooseMode(env);
      if (m == null) {
        throw new EvalException("mode error in FlatPredList "+fp);
      }
      fp.setMode(m);
      env = m.getEnvir();
      cost *= m.getSolutions();
      //System.out.println("DEBUG startEval "+this.hashCode()+" "+fp+" gives cost="+cost);
    }
    outputEnv_ = env;
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
    sLogger.entering("Flatten","visitMemPred");
    assert inputEnv_ != null;
    assert outputEnv_ != null;
    final int end = predlist_.size();
    int curr;
    if (solutionsReturned == 0) {
      // start from the beginning of the list
      solutionsReturned++;
      sLogger.fine("starting search");
      curr = 0;
      if (end == 0) {
        sLogger.exiting("Flatten","visitMemPred",Boolean.TRUE);
        return true;  // we return true just once.
      }
      ((FlatPred)predlist_.get(curr)).startEvaluation();
    }
    else {
      // start backtracking from the end of the list
      sLogger.fine("starting backtracking");
      solutionsReturned++;
      curr = end - 1;
    }
    while (0 <= curr && curr < end) {
      FlatPred fp = (FlatPred)predlist_.get(curr);
      if (fp.nextEvaluation()) {
        curr++;
        if (curr < end) {
          FlatPred nextfp = (FlatPred)predlist_.get(curr);
          sLogger.fine("moving forward to "+curr+": "+nextfp);
          nextfp.startEvaluation();
        } else {
          sLogger.fine("moving forward to "+curr+".");
        }
      }
      else {
        curr--;
        sLogger.fine("moving backwards to "+curr);
     }
    }
    sLogger.exiting("Flatten","visitMemPred",new Boolean(curr == end));
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

  public String toString() {
    StringBuffer result = new StringBuffer();
    for (Iterator i = predlist_.iterator(); i.hasNext(); ) {
      FlatPred p = (FlatPred) i.next();
      result.append(p.toString());
      if (i.hasNext())
        result.append(", ");
    }
    return result.toString();
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
}
