/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2007 Mark Utting

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
import java.io.InputStream;
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
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.DefinitionType;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleUtils;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.PrintVisitor;

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

  /** Maximum acceptable cost for evaluating each FlatPredList */
  private double maxCost_ = 1000000000;

  private static final Logger LOG =
    Logger.getLogger("net.sourceforge.czt.animation.eval");

  private Factory factory_;

  private /*@non_null@*/ Flatten flatten_;

  private /*@non_null@*/ Preprocess preprocess_;

  protected SectionManager sectman_;

  /** Stores the code used in the most recent evaluation. */
  protected FlatPredList predlist_;

  private static long newNameNum = 0;

  private String sectName_;
  private Markup markup_ = Markup.LATEX;

  /** Maximum size of each Given set.  The default is (effectively) infinite. */
  private int givenSetSize_ = Integer.MAX_VALUE;

  /** This can be called to reset the new name counter to 0.
   *  This should be done only before starting an evaluation
   *  that does not rely on the results of any previous evaluation
   *  (otherwise the same name might be generated twice).
   */
  public void resetNewNames()
  {
    newNameNum = 0;
  }

  /** Generates a fresh temporary name. */
  public ZName createNewName()
  {
    return factory_.createZName("tmp"+(newNameNum++));
  }

  /** Recognises the Names produced by createNewName. */
  public /*@pure@*/ static boolean isNewName(/*@non_null@*/ ZName name) {
    String word = name.getWord();
    return word.matches("tmp[0-9]+");
  }

  public ZLive()
  {
    // Make a factory that prints names in ASCII, not Unicode
    // (This is better for debugging and for console output).
    ZFactoryImpl tmp = new ZFactoryImpl();
    tmp.setToStringVisitor(new PrintVisitor(false));
    factory_ = new Factory(tmp);
    flatten_ = new Flatten(this);
    sectman_ = new SectionManager(Dialect.ZPATT);
    sectman_.putCommands(Dialect.ZPATT);
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
                                           + "\\parents standard\\_toolkit"
                                           + "\\end{zsection}",
                                           name);
      specSource.setMarkup(Markup.LATEX);
      sectman_.put(new Key<Source>(name ,Source.class), specSource);
      this.setCurrentSection(name);
    }
    catch (Exception e) {
      System.err.println("ERROR creating " + name + " section: " + e);
      e.printStackTrace();
    }

    // now load the ZLive preprocessing rules.
    try {
      Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
      Key<Source> unfoldKey = new Key<Source>("unfold", Source.class);
      if (sectman_.isCached(unfoldKey))
      {
        if (sectman_.isPermanentKey(unfoldKey))
        {
          System.err.print("Removing permanent key - " + unfoldKey);
          System.err.println(". This will enforce reprocessing.");
        }
        sectman_.removeKey(unfoldKey);
      }
      sectman_.put(unfoldKey, unfoldSource);
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
   * Sets the markup that will be used to parse and print terms.
   */
  public void setMarkup(Markup markup)
  {
      markup_ = markup;
  }

  /**
   * @throws IllegalArgumentException if the given markup is not supported.
   */
  public void setMarkup(String markup)
  {
      markup_ = Enum.valueOf(Markup.class, markup.toUpperCase());
  }

  /** The maximum size of each given set.
   *  This is effectively infinite (actually Integer.MAX_VALUE) by default.
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

  /** Set the maximum acceptable cost for evaluating each FlatPredList.
   *  If the chosen mode has more solutions this, then an exception
   *  will be thrown before evaluation starts.
   */
  public double getSearchSize()
  {
    return maxCost_;
  }

  public void setSearchSize(double num)
  {
    if (num < 1.0)
      throw new CztException("search size must be at least 1.0");
    maxCost_ = num;
  }

  public void setSearchSize(String str)
  {
    setSearchSize(Double.valueOf(str));
  }

  /** Which section evaluations are being done in. */
  public String getCurrentSection()
  {
    return sectName_;
  }

  /** Sets the current section to the one whose name is sectName.
   *  It parses and typechecks the section first.
   *  If sectName is null or empty, a reset is done instead.
   */
  public void setCurrentSection(String sectName)
  throws CommandException
  {
    if (sectName != null && sectName.length() > 0) {
      // parse it then typecheck it
      sectman_.get(new Key<ZSect>(sectName, ZSect.class));
      sectman_.get(new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class));
      sectName_ = sectName;
    }
    else {
      this.reset();
    }
  }

  /** Evaluate a Pred.
   *  This throws some kind of EvalException if pred is too difficult
   *  to evaluate or contains an undefined expression.
   *  The input predicate must have been type checked.
   *  @param pred  A net.sourceforge.czt.z.ast.Pred object.
   *  @return      Usually an instance of TruePred or FalsePred.
   */
  public Pred evalPred(Pred pred)
    throws EvalException
    {
      return (Pred) evalTerm(false, pred, new Envir()).getResult();
    }

  /** Evaluate an Expr.
   *  This throws some kind of EvalException if expr is too difficult
   *  to evaluate or contains an undefined expression.
   *  The input expression must be type checked.
   *  @param expr  A net.sourceforge.czt.z.ast.Expr object.
   *  @return      Usually an instance of EvalSet, or some other expr.
   */
  public Expr evalExpr(Expr expr)
  throws EvalException
  {
    return (Expr) evalTerm(true, expr, new Envir()).getResult();
  }

  /** Evaluate an expression or predicate. */
  public ZLiveResult evalTerm(boolean expr, Term term, Envir env0)
  {
    ZLiveResult result = new ZLiveResult(getCurrentSection(), term);
    if (expr) {
      assert result.isExpr();
      assert ! result.isPred();
    }
    else {
      assert ! result.isExpr();
      assert result.isPred();
    }
    //assert result.isPred() == (! expr);
    //assert result.isExpr() == expr : "Expr is "+term.toString()
    //  + " isPred="+result.isPred() + " and isExpr="+result.isExpr();
    result.setEnvir0(env0);
    compile(result);
    evaluate(result);
    return result;
  }

  /** Processes and compiles a term into internal FlatPred form.
   *  This fills in the unfoldterm, code and mode parts of result.
   * 
   * @param result  resultgetOriginalTerm() is the term to be compiled.
   */
  public void compile(ZLiveResult result)
  {
    LOG.entering("ZLive","compile");
    String section = result.getSectionName();
    FlatPredList predlist = new FlatPredList(this);
    try {
      if (section == null) {
        throw new CztException("Must choose a section!");
      }
      // preprocess the predicate, to unfold things.
      // Unifier.printDepth_ = 7;  // for debugging unifications
      Term unfolded = preprocess_.preprocess(section, result.getOriginalTerm());
      LOG.finer("After preprocess,  pred="+termToString(unfolded));
      result.setUnfoldedTerm(unfolded); // in case typechecking fails...
      // must typecheck, to reestablish the unique-ids invariant.
      typecheck(unfolded);
      LOG.finer("After retypecheck, term="+termToString(unfolded));
      unfolded = preprocess_.fixIds(unfolded);
      LOG.finer("After doing fixIds term="+termToString(unfolded));
      result.setUnfoldedTerm(unfolded);
      if (result.isExpr()) {
        ZName resultName = predlist.addExpr((Expr)unfolded);
        result.setCode(predlist, resultName);
      }
      else {
        predlist.addPred((Pred)unfolded);
        result.setCode(predlist, null);
      }
      Bounds bnds = new Bounds(null);
      // TODO: add any constants in env0 to bnds
      predlist.inferBoundsFixPoint(bnds, INFER_PASSES);
      Envir env0 = result.getEnvir0();
      assert env0 != null;
      LOG.finer("Starting chooseMode with env="+env0.toString());
      Mode m = predlist.chooseMode(env0);
      if (m == null) {
        final String message =
          "Cannot find mode to evaluate: " + termToString(unfolded, markup_);
        throw new EvalException(message);
      }
      LOG.finer("Setting mode "+m.toString());
      result.setMode(m);
      predlist.setMode(m);
    }
    catch (CommandException ex) {
      // we just catch and rethrow this for logging purposes
      LOG.throwing("ZLive", "evalTerm", ex);
      throw new RuntimeException(ex);
    }
    catch (UnboundJokerException ex) {
      // we just catch and rethrow this for logging purposes
      LOG.throwing("ZLive", "evalTerm", ex);
      throw new RuntimeException(ex);
    }
    LOG.exiting("ZLive","compile");
  }

  /** Evaluates a term that has already been preprocessed and compiled.
   *  This fills in the getResult() part of result.
   * 
   * @param result  the code and mode must be already set.
   */
  public void evaluate(ZLiveResult result)
  {
    assert result.getMode() != null;
    try {
      LOG.entering("ZLive","evaluate");
      FlatPredList predlist = result.getCode();
      // throw an exception if this looks too expensive to evaluate
      // TODO: could also move/copy this check into FlatPredList.
      //   (ie. keep track of a more accurate cost by doing the multiplications
      //    as highTide_ advances.  This would prevent huge set comps
      //    from being evaluated and taking too much time).
      double estSolns = result.getMode().getSolutions();
      if (estSolns > maxCost_) {
        StringBuffer msg = new StringBuffer();
        msg.append("Too many solutions -- estimate=");
        msg.append(String.format("%1$.2g", new Object[] {estSolns}));
        msg.append(" [");
        for (Iterator<FlatPred> iter = predlist.iterator(); iter.hasNext(); ) {
          FlatPred fp = iter.next();
          double fpSolns = fp.getMode().getSolutions(); 
          msg.append(String.format("%1$.2g,", new Object[] {fpSolns}));
        }
        msg.deleteCharAt(msg.length()-1);
        msg.append("]");
        throw new EvalException(msg.toString());
      }
      predlist.startEvaluation();
      LOG.finer("Looking for first solution...");
      if (result.isExpr()) {
        if (predlist.nextEvaluation()) {
          ZName resultName = result.getResultName();
          assert resultName != null;
          result.setResult(predlist.getOutputEnvir().lookup(resultName));
        }
        else {
          // In theory this should not happen -- nextEvaluation
          // should have thrown some kind of exception instead.
          CztException ex = new CztException("No solution for expression");
          LOG.throwing("ZLive", "evalTerm", ex);
          throw ex;
        }
      }
      else {
        // evaluate the predicate
        if (predlist.nextEvaluation()) {
          result.setResult(factory_.createTruePred());
        }
        else {
          result.setResult(factory_.createFalsePred());
        }
      }
    }
    catch (RuntimeException ex) {
      // we just catch and rethrow this for logging purposes
      LOG.throwing("ZLive", "evaluate", ex);
      throw ex;
    }
    LOG.exiting("ZLive","evaluate", result);
  }

  /** Converts a schema name into an expression that can be evaluated.
   *  The schema name is looked up in the definition table of the
   *  current section.
   * 
   * @throws CztException if schemaName is not defined.
   *  
   * @param schemaName The undecorated name of a schema.
   * @return           The expression that defines the schema.
   */
  public Expr schemaExpr(String schemaName)
  throws EvalException, CommandException
  {
    Expr schema = null;
    String currSect = getCurrentSection();
    Key<DefinitionTable> key =
      new Key<DefinitionTable>(currSect, DefinitionTable.class);
    DefinitionTable table = getSectionManager().get(key);
    DefinitionTable.Definition def = table.lookup(schemaName);
    // Added distinction with CONSTDECL, for compatibility with old DefinitionTable (Leo)
    if (def != null && def.getDefinitionType().equals(DefinitionType.CONSTDECL))
    {
      schema = def.getExpr();
    }
    if (schema == null)
    {
      CztException ex = new CztException("Cannot find schema: "+schemaName);
      throw ex;
    }
    return schema;
  }

  /** Typechecks a term, to check its correctness and to
   *  reestablish the unique-ids invariant of bound variables.
   *  (bound vars with the same name and scope must have the same id.)
   */
  public void typecheck(Term term)
  throws EvalException, TypeErrorException
  {
    List<? extends ErrorAnn> errors =
      TypeCheckUtils.typecheck(term, sectman_, false, false, getCurrentSection());
    if (errors.size() > 0) {
      throw new TypeErrorException("unfolded term contains type errors", errors);
    }
  }

  /** Prints the given list of FlatPreds.
   */
  public void printCode(FlatPredList code, PrintWriter writer)
  {
    if (code == null || code.size() == 0) {
      writer.println("Code is empty!");
    }
    writer.write(code.toString());
    writer.write("\n");
    writer.flush();
  }
  
  /** Print any term (evaluated or not), using the current markup.
   */
  public void printTerm(PrintStream out, Term term)
  {
    PrintWriter writer = new PrintWriter(out);
    printTerm(writer, term, getMarkup());
  }

  /** Print any term (evaluated or not), using the current markup.
   */
  public void printTerm(PrintWriter writer, Term term)
  {
    printTerm(writer, term, getMarkup());
  }

  /** Write an evaluated term.
   *  The output will be in LaTeX or Unicode format, according to the
   *  current markup setting (see getMarkup()).
   *  Internal ZLive evaluation results, such as EvalSets (which may
   *  contain infinite sets), are converted into standard Z constructs
   *  before they are printed.  For example, each EvalSet enumerates
   *  a maximum number of elements (see the setEvalSetSize methods in
   *  the ResultTreeToZVisitor class) and then prints "..." if there
   *  are more elements remaining.
   */
  public void printTerm(PrintWriter out, Term term0, Markup markup)
  {
    if (term0 == null) {
      out.print("null");
    }
    else {
      try {
        Term term = term0.accept(new ResultTreeToZVisitor());
        PrintUtils.print(term, out, getSectionManager(),
            getCurrentSection(), markup);
      }
      catch (Exception e) {
        out.println("Error: "+e.getLocalizedMessage());
        out.println("while evaluating&printing the result: " + term0);
      }
    }
    out.flush();
  }

  /** Converts the given term to a String. */
  public String termToString(Term term, Markup markup)
  {
    StringWriter stringWriter = new StringWriter();
    printTerm(new PrintWriter(stringWriter), term, markup);
    return stringWriter.toString();
  }

  /** Converts the given term to a String, using the current markup. */
  public String termToString(Term term)
  {
    return termToString(term, getMarkup());
  }

  /**
   * Returns the name and current version of ZLive.
   */
  public static String getBanner()
  {
    return "ZLive version " + getVersion() + ", (C) 2006, Mark Utting";
  }

  /**
   * Returns the version number as a String, or "unknown" if an error
   * occured when accessing the property containing the version
   * information.
   */
  public static String getVersion()
  {
    String version = "unknown";
    try {
      Properties props = new Properties();
      URL url = ZLive.class.getResource("zlive.properties");
      if (url != null) {
        InputStream is = url.openStream();
        try {
          props.load(is);
        } finally {
          is.close();
        }
        version = (String) props.get("version");
      }
    }
    catch (IOException e) {}
    return version;
  }

  public static void main(String args[])
  {
    System.out.println(getBanner());
    System.out.println("To use ZLive from the command line, run TextUI.");
  }

  /** Converts an output BindExpr to an input BindExpr.
   *  That is, it throws away all entries whose names do not end with a
   *  prime, and removes one prime from the entries that do end with a prime.
   *
   * @param expr  Eg. &lt;| x==1, x'==2, y''==3, i?==4, o!==5 |&gt;
   * @return      Eg. &lt;| x==2, y'==3 |&gt;
   */
  public BindExpr unprime(BindExpr expr)
  {
    ZDeclList pairs = factory_.createZDeclList();
    for (Decl decl : expr.getZDeclList()) {
      ConstDecl cdecl = (ConstDecl) decl;
      ZName name = cdecl.getZName();
      ZStrokeList strokes = name.getZStrokeList();
      if (strokes.size() > 0
          && strokes.get(strokes.size()-1) instanceof NextStroke) {
        // copy all strokes except the last
        ZStrokeList newStrokes = factory_.createZStrokeList();
        for (int i=0; i<strokes.size()-1; i++)
          newStrokes.add(strokes.get(i));
        ZName newName = factory_.createZName(name.getWord(), newStrokes);
        pairs.add(factory_.createConstDecl(newName, cdecl.getExpr()));
      }
    }
    return factory_.createBindExpr(pairs);
  }

  public net.sourceforge.czt.z.ast.Expr evalSchema(java.lang.String string ,net.sourceforge.czt.z.ast.BindExpr expr) throws net.sourceforge.czt.session.CommandException { return null; }

  // An example on keeping permanent keys - perhaps the method should be made public or indeed something like loading from a file?
  //class ZLiveSectMan extends SectionManager
  //{
  //  ZLiveSectMan()
  //  {
  //    super();
  //    registerPermanentKey("expansion_rules");
  //    registerPermanentKey("normalization_rules");
  //    registerPermanentKey("predicate_normalization_rules");
  //   registerPermanentKey("simplification_rules");
  //    registerPermanentKey("unfold");
  //  }
  //}
  // All default keys as in util.Section.java
}
