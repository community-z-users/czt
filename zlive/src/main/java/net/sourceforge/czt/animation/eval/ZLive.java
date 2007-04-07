/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

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

import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URL;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Logger;
import java.util.Properties;

import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatPred;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

/** This is the main class of the ZLive animator.
 *  It can be used directly by other Java programs that
 *  want to evaluate Z terms.  It is also used by TextUI,
 *  which provides a text-based user interface for ZLive,
 *  and it could also be used by a GUI class.
 *  
 * @author marku
 *
 */
public class ZLive
{
  /** The maximum number of static inference passes done
   *  prior to mode checking and evaluation.
   *  @see FlatPredList.inferBoundsFixPoint(Bounds,int)
   */
  public static final int INFER_PASSES = 5;

  private static final Logger LOG =
    Logger.getLogger("net.sourceforge.czt.animation.eval");

  private Factory factory_;

  private /*@non_null@*/ Flatten flatten_;

  private /*@non_null@*/ Preprocess preprocess_;

  /** A Writer interface to System.out. */
  protected PrintWriter writer_ = new PrintWriter(System.out);

  protected SectionManager sectman_;

  /** Stores the code used in the most recent evaluation. */
  protected FlatPredList predlist_;

  private static long newNameNum = 0;

  private String sectName_;
  private Markup markup_ = Markup.LATEX;
  
  /** Maximum size of each Given set. */
  private int givenSetSize_ = Integer.MAX_VALUE;

  /** Generates a fresh temporary name. */
  public ZName createNewName()
  {
    // This is a temporary debugging aid, to detect some infinite loops.
    // Once we start evaluating larger terms it will need to be removed
    // (or at least the number increased!).
    if (newNameNum == 554) {
      Exception e = new Exception("infinite loop???  See ZLive.createNewName");
      StringWriter w = new StringWriter();
      e.printStackTrace(new PrintWriter(w));
      LOG.fine("Stack dump: "+w.toString());
    }
    return factory_.createZName("tmp"+(newNameNum++));
  }

  /** Recognises the Names produced by createNewName. */
  public /*@pure@*/ boolean isNewName(/*@non_null@*/ ZName name) {
    String word = name.getWord();
    return word.matches("tmp[0-9]+");
  }

  public ZLive()
  {
    factory_ = new Factory();
    flatten_ = new Flatten(this);
    sectman_ = new SectionManager();
    sectman_.putCommands("zpatt");
    // This prints IDs of ZNames, useful for debugging.
    //sectman_.setProperty(PrintPropertiesKeys.PROP_PRINT_NAME_IDS, "true");
    this.reset();
  }

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
  public void setFactory(Factory fact)
  {
    factory_ = fact;
  }

  /** Get the Preprocess object that is used to unfold terms
   *  before evaluation.
   */
  public Preprocess getPreprocess()
  {
    return preprocess_;
  }

  /** Get the current section manager. */
  public SectionManager getSectionManager()
  { return sectman_; }

   /** Set the section manager that will be used during evaluation. */
  //@ requires sm != null;
  public void setSectionManager(SectionManager sm)
  { sectman_ = sm; }

  /** Reset the section manager that will be used during evaluation.
   *  This clears all the specifications that have been loaded.
   */
  public void reset()
  {
    sectman_.reset();
    final String name = "ZLiveDefault";
    try {
      Source specSource = new StringSource("\\begin{zsection} "
                                           + "\\SECTION " + name + " "
                                           + "\\parents standard\\_toolkit "
                                           + "\\end{zsection}",
                                           name);
      specSource.setMarkup(Markup.LATEX);
      sectman_.put(new Key(name ,Source.class), specSource);
      this.setCurrentSection(name);
    }
    catch (Exception e) {
      System.err.println("ERROR creating " + name + " section: " + e);
      e.printStackTrace();
    }

    // now load the ZLive preprocessing rules.
    try {
      Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
      sectman_.put(new Key("unfold", Source.class), unfoldSource);
      preprocess_ = new Preprocess(sectman_);
      preprocess_.setRules("/preprocess.tex");
    } catch (Exception e) {
      System.err.println("ERROR loading rules from preprocess.tex: " + e);
      e.printStackTrace();
    }
  }

  /** Get a flatten visitor. */
  public Flatten getFlatten()
  { return flatten_; }

  public Markup getMarkup()
  {
    return markup_;
  }

  /**
   * @throws IllegalArgumentException if the given markup is not supported.
   */
  public void setMarkup(String markup)
  {
      markup_ = Enum.valueOf(Markup.class, markup);
  }

  /** The maximum size of each given set. 
   *  This is Integer.MAX_VALUE by default.
   */
  public int getGivenSetSize()
  {
    return givenSetSize_;
  }

  /** Set the maximum size of all given sets.
   *  Note that this setting restricts on the semantics
   *  of the specification, so small values are likely to
   *  change the results of evaluations.
   *
   * @throws NumberFormatException if the argument
   *  string is not a positive integer.
   */
  public void setGivenSetSize(String value)
  {
    givenSetSize_ = Integer.parseInt(value);
  }

  public void setMarkup(Markup markup)
  {
    markup_ = markup;
  }

  /** Which section evaluations are being done in. */
  public String getCurrentSection()
  {
    return sectName_;
  }

  public void setCurrentSection(String sectName)
  throws CommandException
  {
    if (sectName != null && sectName.length() > 0) {
      sectman_.get(new Key(sectName, ZSect.class));          // parse it
      sectman_.get(new Key(sectName, SectTypeEnvAnn.class)); // typecheck it
      sectName_ = sectName;
    }
    else {
      this.reset();
    }
  }

  /** Evaluate a Pred.
      This throws some kind of EvalException if pred is too difficult
      to evaluate or contains an undefined expression.
      The input predicate must be type checked.
      @param pred  A net.sourceforge.czt.z.ast.Pred object.
      @return      Usually an instance of TruePred or FalsePred.
  */
  public Pred evalPred(Pred pred)
    throws EvalException
    {
    LOG.entering("ZLive","evalPred");
    Pred result = null;
    predlist_ = new FlatPredList(this);
    try {
      if (getCurrentSection() == null) {
        throw new CztException("Must choose a section!");
      }
      // preprocess the predicate, to unfold things.
      pred = (Pred) preprocess_.preprocess(getCurrentSection(), pred);
      LOG.finer("After preprocess,  pred="+printTerm(pred));
      // must typecheck, to reestablish the unique-ids invariant.
      typecheck(pred);
      LOG.finer("After retypecheck, pred="+printTerm(pred));
      pred = (Pred) preprocess_.fixIds(pred);
      LOG.finer("After doing fixIds pred="+printTerm(pred));
      predlist_.addPred(pred);
      Envir env0 = new Envir();
      Bounds bnds = new Bounds(null);
      predlist_.inferBoundsFixPoint(bnds, INFER_PASSES);
      Mode m = predlist_.chooseMode(env0);
      if (m == null) {
        final String message =
          "Cannot find mode to evaluate " + pred +
          " (" + printTerm(pred, markup_) + ")";
        throw new EvalException(message);
      }
      predlist_.setMode(m);
      predlist_.startEvaluation();
      if (predlist_.nextEvaluation())
        result = factory_.createTruePred();
      else
        result = factory_.createFalsePred();
    }
    catch (RuntimeException ex) {
      // we just catch and rethrow this for logging purposes
      LOG.throwing("ZLive", "evalPred", ex);
      throw ex;
    }
    LOG.exiting("ZLive","evalPred");
    return result;
    }

  /** Evaluate an Expr.
      This throws some kind of EvalException if expr is too difficult
      to evaluate or contains an undefined expression.
      The input expression must be type checked.
      @param expr  A net.sourceforge.czt.z.ast.Expr object.
      @return      Usually an instance of EvalSet, or some other expr.
  */
  public Expr evalExpr(Expr expr)
  throws EvalException
  {
    LOG.entering("ZLive","evalExpr");
    Expr result = null;
    predlist_ = new FlatPredList(this);
    try {
      if (getCurrentSection() == null) {
        throw new CztException("Must choose a section!");
      }
      // preprocess the expr, to unfold things.
      // Unifier.printDepth_ = 7;  // for debugging unifications
      expr = (Expr) preprocess_.preprocess(getCurrentSection(), expr);
      LOG.finer("After preprocess, expr="+printTerm(expr));
      // must typecheck, to reestablish the unique-ids invariant.
      typecheck(expr);
      LOG.finer("After second typecheck, expr="+printTerm(expr));
      expr = (Expr) preprocess_.fixIds(expr);
      LOG.finer("After doing fixIds hack expr="+printTerm(expr));
      ZName resultName = predlist_.addExpr(expr);
      Bounds bnds = new Bounds(null);
      predlist_.inferBoundsFixPoint(bnds, INFER_PASSES);
      Envir env0 = new Envir();
      Mode m = predlist_.chooseMode(env0);
      if (m == null) {
        final String message =
          "Cannot find mode to evaluate " + expr +
          " (" + printTerm(expr, markup_) + ")";
        throw new EvalException(message);
      }
      predlist_.setMode(m);
      predlist_.startEvaluation();
      if ( ! predlist_.nextEvaluation()) {
        throw new CztException("No solution for expression");
      }
      result = predlist_.getOutputEnvir().lookup(resultName);
    }
    catch (RuntimeException ex) {
      // we just catch and rethrow this for logging purposes
      LOG.throwing("ZLive", "evalExpr", ex);
      throw ex;
    }
    LOG.exiting("ZLive","evalExpr");
    return result;
  }

  /** Evaluate a schema with some given inputs/output.
   *  This calls evalExpr(exists binding @ schema).
   *  The expressions in the BindExpr must be type checked.
   *  @param expr  A net.sourceforge.czt.z.ast.Pred object.
   *  @return      An instance of EvalSet.
  */
  public Expr evalSchema(String schemaName, BindExpr args)
  throws EvalException, CommandException
  {
    String currSect = getCurrentSection();
    Key key = new Key(currSect, DefinitionTable.class);
    DefinitionTable table = (DefinitionTable) getSectionManager().get(key);
    SchText schText = factory_.createZSchText(args.getZDeclList(), factory_.createTruePred());
    Expr schema = table.lookup(schemaName).getExpr();
    if (schema == null) {
      CztException ex =new CztException("Cannot find schema: "+schemaName);
      throw ex;
    }
    ExistsExpr expr = factory_.createExistsExpr(schText, schema);
    LOG.fine("evalSchema is starting to evaluate: "+printTerm(expr));
    return evalExpr(expr);
  }

  /** Typechecks a term, to check its correctness and to
   *  reestablish the unique-ids invariant of bound variables.
   *  (bound vars with the same name and scope must have the same id.)
   */
  public void typecheck(Term term)
  throws EvalException
  {
    List<? extends ErrorAnn> errors =
      TypeCheckUtils.typecheck(term, sectman_, false, getCurrentSection());
    if (errors.size() > 0) {
      StringBuffer buf = new StringBuffer();
      buf.append("Error: unfolded term contains type errors.\n");
      //print any errors
      for (ErrorAnn next : errors) {
        buf.append(next);
      }
      throw new EvalException(buf.toString());
    }
  }

  public void printCode()
  {
    printCode(writer_);
  }

  /** Prints the list of FlatPreds used in the last call
    * to evalPred or evalExpr.
    */
    public void printCode(PrintWriter writer)
    {
      if(predlist_ == null) {
        writer.println("No previous evaluations");
      }
      else {
        try {
          if (predlist_.size() == 0)
            writer.println("Code is empty!");
          for (Iterator i = predlist_.iterator(); i.hasNext(); ) {
            FlatPred p = (FlatPred) i.next();
            writer.write("  " + p.toString() + "\n");
          }
          writer.flush();
        }
        catch (Exception e) {
          e.printStackTrace();
        }
      }
    }

  /** Prints an evaluated expression as a standard text string.
   */
  public void printTerm(PrintStream out, Term term, Markup markup)
  {
    PrintWriter writer = new PrintWriter(out);
    printTerm(writer, term, markup);
    writer.flush();
  }

  /** Writes an evaluated expression as a standard text string.
   *  TODO: improve this to handle GivenValue, SetComp and all
   *        other classes in net.sourceforge.czt.animation.eval.result.
   *        Note that these may be recursive, so we need a visitor.
   */
  public void printTerm(PrintWriter out, Term term, Markup markup)
  {
    if (term == null) {
      out.print("null");
    }
    else if (term instanceof NumExpr) {
      NumExpr num = (NumExpr) term;
      ZNumeral znum = (ZNumeral) num.getNumeral();
      out.print(znum.getValue());
    }
    else if (term instanceof EvalSet) {
      EvalSet set = (EvalSet) term;
      out.print("{ ");
      Iterator<Expr> i = set.iterator();
      while (i.hasNext()) {
        printTerm(out, (Expr) i.next(), markup);
        if (i.hasNext())
          out.print(", ");
      }
      out.print(" }");
    }
    else {
      if (Markup.LATEX.equals(markup)) {
        try {
          PrintUtils.printLatex(term, out, getSectionManager(),
                                getCurrentSection());
          out.flush();
          return;
        }
        catch (Exception e) {
          e.printStackTrace(System.err);
        }
      }
      try {
        PrintUtils.printUnicode(term, out, getSectionManager());
        out.flush();
        return;
      }
      catch (Exception e) {
        e.printStackTrace(System.err);
      }
      out.print(term);
    }
    out.flush();
  }

  /** Converts the given term to a String. */
  public String printTerm(Term term, Markup markup)
  {
    StringWriter stringWriter = new StringWriter();
    printTerm(new PrintWriter(stringWriter), term, markup);
    return stringWriter.toString();
  }

  /** Converts the given term to a String, using the current markup. */
  public String printTerm(Term term)
  {
    return printTerm(term, getMarkup());
  }

  /**
   * Returns the name and current version of ZLive
   */
  public static String getBanner()
  {
    String version = "unknown";
    try {
      Properties props = new Properties();
      URL url = ZLive.class.getResource("zlive.properties");
      if (url != null) {
        props.load(url.openStream());
        version = (String) props.get("version");
      }
    }
    catch (IOException e) {}
    return "ZLive version " + version + ", (C) 2006, Mark Utting";
  }

  public static void main(String args[])
  {
    System.out.println(getBanner());
    System.out.println("To use ZLive from the command line, run TextUI.");
  }
}
