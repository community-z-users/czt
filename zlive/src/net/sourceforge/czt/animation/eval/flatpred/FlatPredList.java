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

import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
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
 *  <pre>
 *  // Stage 1: Setup.
 *  predlist = new FlatPredList( ...a Flatten object...);
 *  ... now add decls, preds, and expressions...
 *  RefName resultName = predlist.addExpr(expr);
 *  Envir env0 = new Envir(); // empty environment
 *
 *  // Stage 2: Optimisation.
 *  // Ask the FlatPredList to optimise itself for
 *  // efficient evaluation, given the inputs in env0.
 *  Mode m = predlist.chooseMode(env0);
 *  if (m == null)
 *    throw new EvalException("Cannot find mode to evaluate " + expr);
 *  predlist.setMode(m);
 *  
 *  // Stage 3: Evaluation.
 *  predlist.startEvaluation();
 *  while (predlist.nextEvaluation())
 *      // lookup the result and do something with it.
 *      System.out.println(predlist.getOutputEnvir().lookup(resultName));
 *  </pre>
 * @czt.todo make this inherit from FlatPred.
 */
public class FlatPredList
{
  private static final Logger LOG
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  /** Maximum number of bounds-inference passes done over the list. */
  protected static final int inferPasses_ = 5;

  /** This stores the list of FlatPreds used in the current evaluation. */
  protected List<FlatPred> predlist_ = new ArrayList<FlatPred>();
  
  /** Records the bound variables in this list
   *  (Ignoring the tmp vars produced by Flatten).
   *  In fact, it contains BOTH the DeclName and RefName form of each bound var.
   *  It is set up as Declarations are added.
   */
  protected /*@non_null@*/ Set<ZDeclName> boundVars_ = new HashSet();

  /** Records the free variables used in this list.
   *  This is calculated and cached by the freeVars() method.
   */
  protected Set<ZRefName> freeVars_;
  
  /** The ZLive animator that owns/uses this FlatPred list. */
  private /*@non_null@*/ ZLive zlive_;
  
  /** Used to flatten a predicate into a list of FlatPreds. */
  /*@non_null@*/ Flatten flatten_;
  
  protected /*@non_null@*/ Factory factory_;
  
  /** A Writer interface to System.out. */
  protected Writer writer = new BufferedWriter(new OutputStreamWriter(System.out));

  private final static BitSet empty_ = new BitSet();
  
  private ModeList evalMode_;

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
  public /*@non_null@*/ Iterator<FlatPred> iterator()
  { return predlist_.iterator(); }

  /** Returns the bound variables of this FlatPredList,
   *  ignoring any temporary variables.
   *  It contains BOTH the DeclName and RefName forms of each bound variable.
   */
  public /*@non_null@*/ Set<ZDeclName> boundVars()
  { return boundVars_; }

  /** Returns the free variables of all the FlatPreds. */
  public /*@non_null@*/ Set<ZRefName> freeVars() {
    if (freeVars_ == null) {
      freeVars_ = new HashSet<ZRefName>();
      for (FlatPred flat : predlist_) {
	for (ZRefName var : flat.freeVars()) {
	  if ( ! zlive_.isNewName(var)) {
	    ZDeclName dvar = (ZDeclName) var.getDecl(); //TODO: check cast
	    if (dvar == null)
	      // TODO: this should never happen, because all ZRefNames
	      // should be linked to a DeclName after typechecking.
	      // For now, we create the corresponding ZDeclName
	      dvar = factory_.createZDeclName(var.getWord(),
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
  public void addSchText(/*@non_null@*/ZSchText stext) {
    for (Decl d : stext.getZDeclList())
      addDecl(d);
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
        ZRefName typeName = flatten_.flattenExpr(type, predlist_);
        for (DeclName name : vdecl.getDeclName()) {
          ZDeclName dvar = (ZDeclName) name;
          boundVars_.add(dvar);
          ZRefName varref = factory_.createZRefName(dvar);
          predlist_.add(new FlatMember(typeName, varref));
        }
      }
      else if (decl instanceof ConstDecl) {
        ConstDecl cdecl = (ConstDecl) decl;
        ZDeclName dvar = cdecl.getZDeclName();
        boundVars_.add(dvar);
        Expr expr = cdecl.getExpr();
        ZRefName varref = factory_.createZRefName(dvar);
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
  public ZRefName addExpr(/*@non_null@*/Expr expr) {
    try {
      return flatten_.flattenExpr(expr,predlist_);
    }
    catch (CommandException exception) {
      throw new EvalException(exception);
    }
  }

  /** Infer bounds for any integer variables.
   *  See FlatPred.inferBounds(Bounds bnds);
   *  <p>
   *  This does upto inferPasses_ passes over all the predicates
   *  in the list (it stops if a fixed point is found earlier).
   *  </p>
   *  @param bnds  The database of lower and upper bounds for integer variables.
   *  @return      true iff the bnds database has been changed at all.
   */
  public boolean inferBounds(Bounds bnds)
  {
    // bnds has changed during this method
    boolean anyChange = false;
    // bnds has changed during most recent pass of predlist_
    boolean recentChange = true;
    for (int i = 0; recentChange && i < inferPasses_; i++) {
      recentChange = false;
      for (FlatPred pred : predlist_) {
        if (pred.inferBounds(bnds))
          recentChange = true;
      }
      anyChange |= recentChange;
    }
    return anyChange;
  }

  /** Optimises the list and chooses a mode.
   *  @czt.todo Implement a simple reordering algorithm here.
   *  The current implement does no reordering.
   */
  public ModeList chooseMode(Envir env0)
  {
    LOG.entering("FlatPredList","chooseMode",env0);
    List<Mode> submodes = new ArrayList<Mode>();
    Envir env = env0;
    double cost = 1.0;
    Iterator i = predlist_.iterator();
    LOG.finer(this.hashCode()+" starting");
    while (i.hasNext()) {
      FlatPred fp = (FlatPred)i.next();
      Mode m = fp.chooseMode(env);
      if (m == null) {
	LOG.exiting("FlatPredList","chooseMode",null);
        return null;
      }
      submodes.add(m);
      env = m.getEnvir();
      cost *= m.getSolutions();
      LOG.finer(this.hashCode()+" "+fp+" gives cost="+cost);
    }
    ModeList result = new ModeList(env, empty_, cost, submodes);
    LOG.exiting("FlatPredList","chooseMode",result);
    return result;
  }

 /** Set the mode that will be used to evaluate this list.
  *  @param mode Must be one of the modes returned previously by chooseMode.
  */
  //@ requires mode instanceof ModeList;
  //@ ensures evalMode_ == mode;
  public void setMode(/*@non_null@*/Mode mode)
  {
    evalMode_ = (ModeList)mode;

    // set modes of all the flatpreds in the list.
    Iterator preds = predlist_.iterator();
    Iterator modes = evalMode_.iterator();
    while (preds.hasNext())
      ((FlatPred)preds.next()).setMode((Mode)modes.next());

    solutionsReturned = -1;
  }

  /** Starts a fresh evaluation.
   */
  //@ requires evalMode_ != null;
  public void startEvaluation()
  {
    LOG.entering("FlatPredList","startEvaluation");
    assert evalMode_ != null;
    solutionsReturned = 0;
    LOG.exiting("FlatPredList","startEvaluation");
   }

  /** The output environment of this FlatPred list.
   *  This is only valid after startEvaluation.
   */
  //@ requires evalMode_ != null;
  public Envir getOutputEnvir() {
    return evalMode_.getEnvir();
  }

  /** Returns the next solution from this list of FlatPreds.
   *  This implements chronological backtracking, like Prolog.
   *  If it returns true, the output environment, available via
   *  getOutputEnvir(), will contain updated values for any bound
   *  variables defined within this FlatPredList.
   *  Note that the empty list of FlatPreds will return true once.
   *  @return true iff a new solution was found.
   */
  public boolean nextEvaluation() {
    LOG.entering("FlatPredList","nextEvaluation");
    final int end = predlist_.size();
    int curr;
    if (solutionsReturned == 0) {
      // start from the beginning of the list
      solutionsReturned++;
      LOG.fine("starting search, size=" + end);
      curr = 0;
      if (curr < end)
	((FlatPred)predlist_.get(curr)).startEvaluation();
      else {
	// curr==end==0, so we do not enter the loop below at all.
	// The result will be true.
      }
    }
    else {
      // start backtracking from the end of the list
      LOG.fine("starting backtracking");
      solutionsReturned++;
      curr = end - 1;
    }
    // invariant: the output env contains a valid solution for predlist[0..curr-1]
    while (0 <= curr && curr < end) {
      FlatPred fp = (FlatPred)predlist_.get(curr);
      if (fp.nextEvaluation()) {
        curr++;
        if (curr < end) {
          FlatPred nextfp = (FlatPred)predlist_.get(curr);
          LOG.fine("moving forward to "+curr+": "+nextfp);
          nextfp.startEvaluation();
        } else {
          LOG.fine("moving forward to "+curr+".");
        }
      }
      else {
        curr--;
        LOG.fine("moving backwards to "+curr);
     }
    }
    LOG.exiting("FlatPredList","nextEvaluation",new Boolean(curr == end));
    return curr == end;
  }

  /** Prints the list of FlatPreds used in the last call
    * to evalPred or evalExpr.
    */
  public void printCode()
  {
    try {
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
