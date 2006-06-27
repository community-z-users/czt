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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.Flatten;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.ZRefNameComparator;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;

/** Manages a list of FlatPred predicates.
 *  Provides methods for adding declarations and predicates
 *  to the list, doing mode analysis of the list, and
 *  evaluating the list (giving a series of updated environments).
 *  <p>
 *  Here is a typical use of FlatPredList:
 *  </p>
 *  <pre>
 *  // Stage 1: Setup.
 *  predlist = new FlatPredList(zlive_instance);
 *  // now add decls, predicates, expressions etc.
 *  ZRefName resultName = predlist.addExpr(expr);
 *  Envir env0 = new Envir(); // empty environment
 *
 *  // Stage 2: Optimisation.
 *  predlist.inferBounds(new Bounds()); // does some static analysis
 *  // Ask the FlatPredList to optimise itself for efficient
 *  // evaluation, given the inputs in env0 (none in this case).
 *  Mode m = predlist.chooseMode(env0);
 *  if (m == null)
 *    throw new EvalException("Cannot find mode to evaluate " + expr);
 *  predlist.setMode(m);
 *  
 *  // Stage 3: Evaluation.
 *  predlist.startEvaluation();
 *  while (predlist.nextEvaluation())
 *      // lookup the result and do something with it.
 *      System.out.println(predlist.getEnvir().lookup(resultName));
 *  </pre>
 */
public class FlatPredList extends FlatPred
{
  /** Maximum number of bounds-inference passes done over the list. */
  protected static final int inferPasses_ = 5;

  public static final boolean optimize = false;

  /** This stores the list of FlatPreds used in the current evaluation. */
  protected List<FlatPred> predlist_ = new ArrayList<FlatPred>();
  
  /** Records the bound variables in this list
   *  (Ignoring the tmp vars produced by Flatten).
   *  In fact, it contains BOTH the DeclName and RefName form of each bound var.
   *  It is set up as Declarations are added.
   */
  protected/*@non_null@*/Set<ZDeclName> boundVars_
    = new HashSet<ZDeclName>();
  
  /** The ZLive animator that owns/uses this FlatPred list. */
  private /*@non_null@*/ ZLive zlive_;
  
  /** Creates an empty FlatPred list. */
  public FlatPredList(ZLive newZLive) 
  {
    zlive_ = newZLive;
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

  /** Returns the free variables of all the FlatPreds.
   *  This must not be called until after all addPred/Expr
   *  calls have been done.  The first time it is called, it
   *  calculates the free variables as the union of the free
   *  variables of all the FlatPreds in the list.
   *  It also sets the args list to contain these same variables.
   */
  @Override public /*@non_null@*/ Set<ZRefName> freeVars() {
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
              dvar = getFactory().createZDeclName(var.getWord(),
                  var.getStrokeList(),
                  null);
            if ( ! boundVars_.contains(dvar))
              freeVars_.add(var);
          }
        }
      }
      args_ = new ArrayList<ZRefName>(freeVars_);
      Collections.sort(args_, ZRefNameComparator.create()); // so the order is reproducible
    }
    return freeVars_;
  }

  /** @inheritDoc
   *  The first time this is called, it calculates freeVars and
   *  sets <code>args</code> to contain the same set of variables.
   */
  @Override public List<ZRefName> getArgs()
  {
    if (freeVars_ == null)
      freeVars();  // calculate freeVars and args.
    return args_;
  }

  /** Add one FlatPred to the FlatPred list.
   *  This is a low-level method, and addDecl or addPred
   *  should usually be used in preference to this method.
   *  This method should be called before chooseMode 
   *  or freeVars are called.
   *
   * @param flat  the FlatPred to add.
   */
  public void add(/*@non_null@*/FlatPred flat)
  {
    assert freeVars_ == null;
    predlist_.add(flat);
  }

  /** Adds a whole schema text to the FlatPred list.
   *  This method should be called before chooseMode 
   *  or freeVars are called.
   *
   * @param stext 
   */
  public void addSchText(/*@non_null@*/ZSchText stext)
  {
    assert freeVars_ == null;
    for (Decl d : stext.getZDeclList())
      addDecl(d);
    Pred p = stext.getPred();
    if (p != null)
      addPred(p);
  }
  
  /** Adds one declaration to the FlatPred list.
   *  This converts x,y:T into x \in T \land y \in T.
   *  (More precisely, into: tmp=T; x \in tmp; y \in tmp).
   *  This method should be called before chooseMode
   *  or freeVars are called.
   *
   * @param decl  May declare several variables.
   */
  public void addDecl(/*@non_null@*/Decl decl)
  {
    assert freeVars_ == null;
    try {
      if (decl instanceof VarDecl) {
        VarDecl vdecl = (VarDecl) decl;
        Expr type = vdecl.getExpr();
        ZRefName typeName = flattenExpr(type, predlist_);
        for (DeclName name : vdecl.getDeclName()) {
          ZDeclName dvar = (ZDeclName) name;
          boundVars_.add(dvar);
          ZRefName varref = getFactory().createZRefName(dvar);
          predlist_.add(new FlatMember(typeName, varref));
        }
      }
      else if (decl instanceof ConstDecl) {
        ConstDecl cdecl = (ConstDecl) decl;
        ZDeclName dvar = cdecl.getZDeclName();
        boundVars_.add(dvar);
        Expr expr = cdecl.getExpr();
        ZRefName varref = getFactory().createZRefName(dvar);
        flattenPred(getFactory().createMemPred(varref, expr), predlist_);
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
   *  This method should be called before chooseMode
   *  or freeVars are called.
   *
   * @param pred  The Pred to flatten and add.
   */
  public void addPred(/*@non_null@*/Pred pred)
  {
    assert freeVars_ == null;
    try {
      flattenPred(pred,predlist_);
    }
    catch (CommandException exception) {
      throw new EvalException(exception);
    }
  }

  /** Adds one expression to the FlatPred list.
   *  This method should be called before chooseMode
   *  or freeVars are called.
   *  Returns the 'result' name that will be bound to the result
   *  of the expression after evaluation.  That is,
   *  after chooseMode, startEvaluation and nextEvaluation have
   *  been called, then getOutputEnvir().lookup(result) can
   *  be called to get the value of the evaluated expression.
   *
   * @param expr  The Expr to flatten and add.
   * @return      The result name.
   */
  public ZRefName addExpr(/*@non_null@*/Expr expr)
  {
    assert freeVars_ == null;
    try {
      return flattenExpr(expr,predlist_);
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
    LOG.entering("FlatPredList","inferBounds",bnds);
    // bnds has changed during this method
    boolean anyChange = false;
    // bnds has changed during most recent pass of predlist_
    boolean recentChange = true;
    for (int i = 0; recentChange && i < inferPasses_; i++) {
      LOG.fine("Starting inferBounds pass " + (i+1) + " with bounds="+bnds);
      recentChange = false;
      for (FlatPred pred : predlist_) {
        if (pred.inferBounds(bnds)) {
          LOG.finer("changed bounds of "+pred);
          recentChange = true;
        }
      }
      anyChange |= recentChange;
    }
    LOG.exiting("FlatPredList","inferBounds",anyChange);
    return anyChange;
  }

  /** Optimises the list and chooses a mode.
   *  Note that inferBounds should usually be done before this,
   *  since it may narrow the search space of chooseMode.
   *  
   *  @czt.todo Implement a simple reordering algorithm here.
   *  The current implementation does no reordering.
   */
  public ModeList chooseMode(Envir env0)
  {
    LOG.entering("FlatPredList", "chooseMode", env0);
    List<FlatPred> flatPreds = new ArrayList<FlatPred>(predlist_);
    List<Mode> submodes = new ArrayList<Mode>();
    Envir env = env0;
    getArgs(); // forces freeVars_ and args_ to be evaluated.
    LOG.finer(this.hashCode() + " starting");
    while (!flatPreds.isEmpty() && chooseMode(env, flatPreds, submodes)) {
      env = submodes.get(submodes.size() - 1).getEnvir();
    }
    if ( ! flatPreds.isEmpty()) {
      LOG.finer("no mode for " + flatPreds.get(0) + " with env=" + env);
      LOG.exiting("FlatPredList", "chooseMode", null);
      return null;
    }
    assert submodes.size() == predlist_.size();
    double cost = Mode.ONE_SOLUTION;
    for (Mode m : submodes) {
      cost *= m.getSolutions();
      LOG.finer(this.hashCode() + " " + m.getParent() + " gives cost=" + cost
          + " and outputs=" + m.getOutputs());
    }
    ModeList result = new ModeList(this, env, args_, cost, submodes);
    LOG.exiting("FlatPredList", "chooseMode", result);
    return result;
  }

  /**
   * Removes the corresponding FlatPred from the list
   * when a Mode is inserted into the mode list.
   */
  //@requires ! flatPreds.isEmpty();
  private boolean chooseMode(Envir env0, List<FlatPred> flatPreds,
      List<Mode> modes)
  {
    Mode mode = null;
    if (optimize) {
      // choose first mode with the smallest number of solutions.
      for (Iterator<FlatPred> iter = flatPreds.iterator(); iter.hasNext();) {
        FlatPred flatPred = iter.next();
        Mode m = flatPred.chooseMode(env0);
        if (m != null) {
          assert flatPred == m.getParent();
          if (mode == null || m.getSolutions() < mode.getSolutions())
            mode = m;
        }
      }
    }
    else {
      // do them in the original order.
      mode = flatPreds.get(0).chooseMode(env0);
    }
    if (mode == null)
      return false;
    modes.add(mode);
    boolean removed = remove(mode.getParent(), flatPreds);
    assert removed;
    return true;
  }

  /**
   * Remove the first occurrence of the given element (checked with ==)
   * from the list.
   */
  private boolean remove(Object element, List list)
  {
    boolean removed = false;
    for (Iterator iter = list.iterator(); ! removed && iter.hasNext(); ) {
      Object o = iter.next();
      if (o == element) {
        iter.remove();
        removed = true;
      }
    }
    return removed;
  }

 /** Set the mode that will be used to evaluate this list.
  *  @param mode Must be one of the modes returned previously by chooseMode.
  */
  //@ requires mode instanceof ModeList;
  //@ ensures evalMode_ == mode;
  public void setMode(/*@non_null@*/Mode mode)
  {
    super.setMode(mode);
    ModeList modeList = (ModeList) evalMode_;
    assert modeList.size() == predlist_.size();
    predlist_.clear();
    for (Iterator<Mode> modes = modeList.iterator();
         modes.hasNext(); ) {
      final Mode m = modes.next();
      final FlatPred flatPred = m.getParent();
      predlist_.add(flatPred);
      flatPred.setMode(m);
    }
    assert modeList.size() == predlist_.size();
  }

  /** Starts a fresh evaluation.
   */
  //@ requires evalMode_ != null;
  public void startEvaluation()
  {
    LOG.entering("FlatPredList","startEvaluation");
    super.startEvaluation();
    assert evalMode_ != null;
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
    final int end = predlist_.size(); // points just PAST the last flatpred.
    int curr;
    if (solutionsReturned_ == 0) {
      // start from the beginning of the list
      solutionsReturned_++;
      curr = 0;
      LOG.fine("starting search, size=" + end
          + ((curr < end) ? ": "+predlist_.get(curr) : ""));
      if (curr < end)
        predlist_.get(curr).startEvaluation();
      else {
        // curr==end==0, so we do not enter the loop below at all.
        // The result will be true.
      }
    }
    else {
      // start backtracking from the end of the list
      solutionsReturned_++;
      curr = end - 1;
      LOG.fine("starting backtracking from "+curr);
    }
    // invariant: the output env contains a valid solution for predlist[0..curr-1]
    while (0 <= curr && curr < end) {
      FlatPred fp = predlist_.get(curr);
      if (fp.nextEvaluation()) {
        curr++;
        if (curr < end) {
          FlatPred nextfp = predlist_.get(curr);
          LOG.fine("moving forward to "+curr+": "+nextfp);
          nextfp.startEvaluation();
        } else {
          LOG.fine("producing new solution: "+this.getOutputEnvir());
        }
      }
      else {
        curr--;
        LOG.fine("moving backwards to "+curr
            +((curr >= 0) ? ": "+predlist_.get(curr) : ""));
     }
    }
    LOG.exiting("FlatPredList","nextEvaluation",new Boolean(curr == end));
    return curr == end;
  }

  protected Factory getFactory()
  {
    return zlive_.getFactory();
  }

  protected void flattenPred(Pred toFlatten, List<FlatPred> destination)
    throws CommandException
  {
    zlive_.getFlatten().flattenPred(toFlatten, destination);
  }

  protected ZRefName flattenExpr(Expr toFlatten, List<FlatPred> destination)
    throws CommandException
  {
    return zlive_.getFlatten().flattenExpr(toFlatten, destination);
  }

  public String toString() {
    StringBuffer result = new StringBuffer();
    for (Iterator<FlatPred> i = predlist_.iterator(); i.hasNext(); ) {
      result.append(i.next().toString());
      if (i.hasNext())
        result.append(", ");
    }
    return result.toString();
  }
}
