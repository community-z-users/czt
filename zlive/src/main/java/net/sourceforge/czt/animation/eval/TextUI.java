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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.Stack;
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.flatpred.FlatRangeSet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.ProverUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.SimpleProver;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.ast.ProverJokerExpr;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zpatt.ast.Deduction;
import net.sourceforge.czt.zpatt.ast.RulePara;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.util.Factory;

/** A text-based user interface for the ZLive animator.
 * @author marku
 *
 */
public class TextUI {
  private static Logger LOG
    = Logger.getLogger("net.sourceforge.czt.animation.eval");

  /** The animator engine */
  protected ZLive zlive_;

  /** The current output stream */
  protected PrintWriter output_;

  protected Stack<ZLiveResult> stack_ = new Stack<ZLiveResult>();
  
  /** Get the instance of ZLive that is used for evaluation. */
  public ZLive getZLive()
  {
    return zlive_;
  }

  /** The current output stream for messages and errors. */
  public PrintWriter getOutput()
  {
    return output_;
  }

  /** Set the current output writer. */
  public void setOutput(/*@non_null*/PrintWriter output)
  {
    output_ = output;
  }

  /** main entry point, which runs ZLive with System.in and System.out. */
  public static void main (String args[])
  throws IOException
  {
    BufferedReader input = new BufferedReader(new InputStreamReader(System.in));
    PrintWriter output = new PrintWriter(System.out, true); // with autoflush
    output.println(ZLive.getBanner());

    // save log messages into zlive.log, using our human-readable format
    if (args.length > 0 && args[0].equals("-logrules")) {
      output.println("Logging net.sourceforge.czt.rules...");
      ZFormatter.startLogging("net.sourceforge.czt.rules",
          "zlive.log", Level.FINEST);
    }
    else if (args.length > 0 && args[0].equals("-logeval")) {
      output.println("Logging net.sourceforge.czt.animation.eval...");
      ZFormatter.startLogging("net.sourceforge.czt.animation.eval",
          "zlive.log", Level.FINEST);
    }
    else if (args.length > 0)
      output.println("Usage: [-logrules | -logeval]");

    TextUI ui = new TextUI(new ZLive(), output);
    ui.mainLoop(input);
  }

  /** Constructs a new ZLive textual user interface.
   *  If the output PrintWriter is null, then System.out
   *  is used as the default output device.
   *
   * @param zlive  The animation engine.
   * @param output The output writer (optional).
   */
  public TextUI(ZLive zlive, PrintWriter output)
  {
    zlive_ = zlive;
    if (output == null)
      output_ = new PrintWriter(System.out, true); // with autoflush
    else
      output_ = output;
  }

  /** The main read-process loop. */
  public void mainLoop(BufferedReader input)
  throws IOException
  {
    while (true) {
      String sect = zlive_.getCurrentSection();
      output_.print(sect + "> ");
      output_.flush();
      String str = input.readLine();
      str = str.trim();
      if (str == null || str.equals("quit") || str.equals("exit"))
        break;
      else if ( ! str.equals("")) {
        String parts[] = str.split(" +", 2);
        processCmd(parts[0], parts.length > 1 ? parts[1] : "");
      }
    }
  }

  /** Process one input command.
   *  This handles most of the commands listed in printHelp.
   *  However, 'quit' must be handled by the caller.
   *  Unknown commands are passed on to doUnknownCmd.
   */
  public void processCmd(String cmd, String args)
  {
    assert cmd != null;
    assert args != null;
    try {
      final SectionManager manager = zlive_.getSectionManager();
      if (cmd.equals("load")) {
        String sectName = doLoadSpec(args);
        if (sectName != null) {
          output_.println("Setting section to " + sectName);
          zlive_.setCurrentSection(sectName);
        }
      }
      else if (cmd.equals("eval") || cmd.equals("evalp")) {
        doEvalExprPred(args, output_);
      }
      else if (cmd.equals("do")) {
        Expr expr = parseExpr(args, output_);
        stack_.push(new ZLiveResult(zlive_.getCurrentSection(), expr));
        stack_.peek().setEnvir0(new Envir());
        zlive_.compile(stack_.peek());
        zlive_.evaluate(stack_.peek());
        doMove(1);
      }
      else if (cmd.equals("next")) {
        doMove(+1);
      }
      else if (cmd.equals("curr")) {
        doMove(0);
      }
      else if (cmd.equals("prev")) {
        doMove(-1);
      }
      else if (cmd.equals(";")) {
        Expr oldState = stack_.peek().currentMember();
        if (oldState == null || ! (oldState instanceof BindExpr)) {
          throw new RuntimeException("no current binding to compose with");
        }
        BindExpr inputs = zlive_.unprime( (BindExpr) oldState );
        if (inputs.getZDeclList().size() == 0) {
          throw new CztException("current binding has no primed names");
        }
        Expr schema = parseExpr(args,output_);
        Envir env = new Envir().plusAll(inputs);
        // TODO: prompt user for any missing inputs???
        stack_.push(new ZLiveResult(zlive_.getCurrentSection(), schema));
        stack_.peek().setEnvir0(env);
        zlive_.compile(stack_.peek());
        zlive_.evaluate(stack_.peek());
        doMove(1);
      }
      else if (cmd.equals("undo")) {
        if (stack_.size() == 0) {
          output_.println("Nothing to undo.");
        }
        else {
          stack_.pop();
          if (stack_.isEmpty()) {
            output_.println("Returned to the start.");
          }
          else {
            output_.println("Returned to: " +
                printTerm(stack_.peek().getOriginalTerm(), zlive_.getMarkup()));
            doMove(stack_.peek().currentPosition());
          }
        }
      }
      else if (cmd.equals("why")) {
        zlive_.printCode(stack_.peek().getCode(), output_);
      }
      else if (cmd.equals("set")) {
        if (args == null || "".equals(args))
          printSettings(output_);
        else {
          final String parts[] = args.split(" +", 2);
          final String value = parts.length > 1 ? parts[1] : "";
          setSetting(parts[0], value);
        }
      }
      else if (cmd.equals("show")) {
        printTypes(zlive_.getCurrentSection());
      }
      else if (cmd.equals("conjectures")) {
        doConjectures();
      }
      else if (cmd.equals("reset")) {
        zlive_.reset();
        stack_.clear();
        output_.println("All specifications cleared...");
      }
      else if (cmd.equals("ver") || cmd.equals("version")) {
        output_.println(ZLive.getBanner());
      }
      else if (cmd.equals("help")) {
        printHelp(output_);
      }
      else if (cmd.equals("env")) {
        final String section = zlive_.getCurrentSection();
        if (section != null) {
          output_.println(manager.get(new Key(section, OpTable.class)));
          output_.println(manager.get(new Key(section, DefinitionTable.class)));
        }
      }
      else if (cmd.equals("unfold")) {
        Term term = parseTerm(args, output_);
        term = unfoldTerm(term);
        if (term != null)
          output_.println("Term = "+zlive_.printTerm(term));
      }
      else if (cmd.equals("apply")) {
        doApplyRule(args);
      }
      else {
        doUnknownCmd(cmd, args);
      }
    }

    // Now handle the various kinds of exceptions that we expect.
    catch (UndefException ex)
    {
      output_.println("Undefined!  " + ex.getMessage());
      if (ex.getTerm() != null) {
        output_.print("    term = ");
        printTerm(output_, ex.getTerm(), zlive_.getMarkup());
        output_.println();
      }
    }
    catch (EvalException ex)
    {
      output_.println();
      output_.println("Error: evaluation too difficult/large: "
          + ex.getMessage());
      if (ex.getTerm() != null) {
        output_.print("    term = ");
        printTerm(output_, ex.getTerm(), zlive_.getMarkup());
        output_.println();
      }
    }
    catch (SourceLocator.SourceLocatorException ex) {
      output_.println("Cannot find source for section '" + ex.getName() + "'");
    }
    catch (Exception ex) {
      output_.println("Error: " + ex.getMessage());
      // ex.printStackTrace();
    }
    output_.flush();
  }

  /** This is called for commands that processCmd does not handle.
   *  The default implementation just prints an error message.
   *  However, it could be overridden to handle additional commands.
   * @param cmd
   * @param args
   */
  public void doUnknownCmd(String cmd, String args)
  {
    output_.println("Invalid command.  Try 'help'");
  }

  /** Loads the given specification file into ZLive. */
  public String doLoadSpec(String filename)
  throws CommandException
  {
    final SectionManager manager = zlive_.getSectionManager();
    Key key = new Key(filename, Spec.class);
    if (manager.isCached(key))
    {
      output_.println(filename + " is already loaded.");
      output_.println("Do a reset before you reload a specification.");
      return null;
    }
    else
    {
      Source source = new FileSource(filename);
      manager.put(new Key(filename, Source.class), source);
      Spec spec = (Spec) manager.get(key);
      String sectName = null;
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          sectName = ((ZSect) sect).getName();
          output_.println("Loading section " + sectName);
          Key typekey = new Key(sectName, SectTypeEnvAnn.class);
          /* ignore the result */  manager.get(typekey);
        }
      }
      if (sectName == null) {
        output_.println("Warning: " + filename + " contains no Z!");
      }
      return sectName;
    }
  }

  public void doEvalExprPred(String args, PrintWriter out)
  throws IOException, CommandException
  {
    Term term = parseTerm(args, out);
    if (term == null)
      return;
    LOG.fine("Starting to evaluate: " + term);
    Term result = null;
    if (term instanceof Pred)
      result = zlive_.evalPred( (Pred)term );
    else
      result = zlive_.evalExpr( (Expr)term );
    if (result != null)
      printTerm(out, result, zlive_.getMarkup());
    out.println();
  }

  protected void doMove(int offset)
  {
    if (stack_.isEmpty()) {
      throw new RuntimeException("you need to use 'do' to evaluate a set/schema first.");
    }
    ZLiveResult result = stack_.peek();
    result.moveTo(result.currentPosition() + offset);
    output_.print(result.currentPosition()+": ");
    this.printTerm(output_, result.currentMember(), zlive_.getMarkup());
    output_.println();
  }
  
  /** Tries to prove all the conjectures in the current section.
   *  Proof consists of exhaustively checking all possible instantiations
   *  of the conjecture, which is similar to model-checking.
   *  This command means that conjectures are a convenient way
   *  of storing ZLive examples and regression tests in a Z section.
   */
  public void doConjectures()
  throws CommandException
  {
    SectionManager manager = zlive_.getSectionManager();
    final String section = zlive_.getCurrentSection();
    if (section == null) {
      output_.println("Error: no current section.");
    }
    else {
      ZSect sect = (ZSect) manager.get(new Key(section, ZSect.class));
      for (Para par : ZUtils.assertZParaList(sect.getParaList()))
        if (par instanceof ConjPara) {
          ConjPara conj = (ConjPara) par;
          LocAnn loc = (LocAnn) par.getAnn(LocAnn.class);
          if (loc != null) {
            output_.println("Conjecture on line "+loc.getLine());
          }
          try {
            printTerm(output_, zlive_.evalPred( conj.getPred() ), zlive_.getMarkup());
            output_.println();
          }
          catch (Exception e) {
            output_.println("Error: "+e);
            output_.println("  in: ");
            zlive_.printTerm(output_, conj.getPred(), zlive_.getMarkup());
            e.printStackTrace(output_);
          }
        }
      output_.println();
    }
  }

  /** Implements the 'apply rulename expr' command.
   *  This is useful for debugging rules.
   * @param args
   * @throws CommandException
   * @throws IOException
   * @throws UnboundJokerException
   */
  public void doApplyRule(String args)
  throws CommandException, IOException, UnboundJokerException
  {
    SectionManager manager = zlive_.getSectionManager();
    String section = zlive_.getCurrentSection();
    final String parts[] = args.split(" +", 2);
    if (parts.length > 1) {
      Source src = new StringSource(parts[1]);
      Markup markup = zlive_.getMarkup();
      src.setMarkup(markup);
      Expr expr = ParseUtils.parseExpr(src, section, manager);
      List<? extends ErrorAnn> errs = TypeCheckUtils.typecheck(expr, manager, false, section);
      if (errs.size() > 0)
        output_.println("Type errors: "+errs);
      RuleTable rules = (RuleTable)
      manager.get(new Key("ZLivePreprocess", RuleTable.class));
      RulePara rulePara = rules.get(parts[0]);
      if (rulePara == null) {
        output_.println("Cannot find rule paragraph " + parts[0]);
      }
      else {
        Factory fact = new Factory(new ProverFactory());
        ProverJokerExpr joker = (ProverJokerExpr)
        fact.createJokerExpr("_", null);
        Pred pred = ProverUtils.FACTORY.createEquality(expr, joker);
        Sequent sequent =
          ProverUtils.createSequent(pred, true);
        SimpleProver prover = new SimpleProver(rules, manager, section);
        if (SimpleProver.apply(rulePara, sequent)) {
          Deduction ded = sequent.getAnn(Deduction.class);
          boolean proveresult = prover.prove(ded);
          if (proveresult) {
            Expr result = (Expr) joker.boundTo();
            if (result == null) {
              output_.println("Error: output joker is null -- not bound");
            }
            else {
              output_.println(zlive_.printTerm(ProverUtils.removeJoker(result)));
            }
          }
          else {
            output_.println("Could not prove premiss "+proveresult);
          }
        }
        else {
          output_.println("Cannot apply rule " + parts[0] +
              " to expr " + zlive_.printTerm(expr));
        }
      }
    }
    else {
      output_.println("Command 'apply' requires two arguments.  Try 'help'");
    }
  }

  /** Prints the current values of all the ZLive settings.
   *  NOTE: when you change this, make sure you update printSettingsHelp too.
   */
  public void printSettings(PrintWriter out)
  {
    out.println("markup          = " + zlive_.getMarkup());
    out.println("section         = " + zlive_.getCurrentSection());
    out.println("givensetsize    = " + zlive_.getGivenSetSize());
    out.println("numitersize     = " + RangeSet.getNumIterSize());
    out.println("closedrangesize = " + FlatRangeSet.getAverageClosedRange());
    out.println("searchsize      = " + FlatPredList.getSearchSize());
    out.println("printsetsize    = " + ResultTreeToZVisitor.getEvalSetSize());
  }

  /** Prints a help message about all the settings. */
  public void printSettingsHelp(PrintWriter out)
  {
    out.println("Explanation of ZLive Settings");
    out.println("markup: controls whether LATEX or UNICODE markup is");
    out.println("        used when reading and printing Z terms.");
    out.println("section: determines the context of evaluations.");
    out.println("givensetsize: the maximum size of each given set.");
    out.println("        This is effectively infinite by default, but can be");
    out.println("        set lower if you want to assume finite given sets");
    out.println("        (this may compromise correctness for some specs).");
    out.println("numitersize: how far we try to enumerate large ranges n..m,");
    out.println("        before reporting an EvalException.");
    out.println("closedrangesize: the average estimated size of closed n..m");
    out.println("        ranges, when n and m are unknown.");
    out.println("searchsize: the max acceptable evaluation cost for each predicate.");
    out.println("        If no evaluation mode with less cost than this can be found,");
    out.println("        then evaluation will not be started.");
    out.println("printsetsize: the max number of elements of each set that will be");
    out.println("        printed during output.");
  }

  /** Set one of the ZLive settings to the given value. */
  public void setSetting(String name, String value)
  throws CommandException
  {
    if ("markup".equals(name)) {
      zlive_.setMarkup(value);
    }
    else if ("section".equals(name)) {
      zlive_.setCurrentSection(value);
    }
    else if ("givensetsize".equals(name)) {
      zlive_.setGivenSetSize(value);
    }
    else if ("numitersize".equals(name)) {
      RangeSet.setNumIterSize(value);
    }
    else if ("closedrangesize".equals(name)) {
      FlatRangeSet.setAverageClosedRange(value);
    }
    else if ("searchsize".equals(name)) {
        FlatPredList.setSearchSize(value);
      }
    else if ("printsetsize".equals(name)) {
      ResultTreeToZVisitor.setEvalSetSize(value);
    }
    else {
      output_.println("Unknown setting: " + name);
    }
  }

  /** Prints the ZLive help/usage message */
  public void printHelp(PrintWriter out)
  {
    out.println("\n--------------- ZLive Commands ---------------");
    out.println("load file.tex     -- Read a Z specification into ZLive");
    out.println("eval <expr>       -- Evaluate an expression");
    out.println("evalp <pred>      -- Evaluate a predicate (synonym for eval)");
    out.println("do <expr>         -- Evaluate a schema/set and show one member");
    out.println("next/curr/prev    -- Show next/current/previous state of a schema/set");
    out.println("; schemaExpr      -- Compose the current state with schemaExpr");
    out.println("undo              -- Undo the last 'do' or ';' command.");
    out.println("why               -- Show the internal code of the last command");
    out.println("set               -- Show all current settings");
    out.println("set <var> <value> -- Sets <var> to <value>.");
    out.println("show              -- Show name & type of defns in current section");
    out.println("conjectures       -- Evaluate all conjectures in the current section");
    out.println("reset             -- Remove all loaded specifications");
    out.println("version           -- Display the version of ZLive");
    out.println("help              -- Display this help summary");
    out.println("quit              -- Exit the ZLive program");
    out.println("  env             -- Show internal defn/operator tables");
    out.println("  unfold term     -- Show term after initial unfolding (debug)");
    out.println("  apply rule expr -- Try to rewrite expr using rule (debug)");
    out.println();
    printSettingsHelp(out);
  }

  /** Prints the names and types of the definitions in the given section. */
  public void printTypes(String sectName)
  throws CommandException
  {
    SectTypeEnvAnn types = (SectTypeEnvAnn) zlive_.getSectionManager().get(
        new Key(sectName, SectTypeEnvAnn.class));
    for (NameSectTypeTriple triple : types.getNameSectTypeTriple()) {
      if (triple.getSect().equals(sectName))
        output_.println("    "+triple.getZName()+":  "+triple.getType());
    }
  }

  public String printTerm(Term term, Markup markup)
  {
    StringWriter stringWriter = new StringWriter();
    printTerm(new PrintWriter(stringWriter), term, markup);
    return stringWriter.toString();
  }

  /** Prints an evaluated expression as a standard text string.
   */
  public void printTerm(PrintStream out, Term term, Markup markup)
  {
    PrintWriter writer = new PrintWriter(out);
    printTerm(writer, term, markup);
    writer.flush();
  }

  /** Writes an evaluated expression as LaTeX or Unicode.
   *  This converts most ZLive-specific terms into standard Z terms
   *  then uses the usual print visitors.
   */
  public void printTerm(PrintWriter out, Term term0, Markup markup)
  {
    try {
      Term term = term0.accept(new ResultTreeToZVisitor());
      PrintUtils.print(term, out,
                       zlive_.getSectionManager(),
                       zlive_.getCurrentSection(),
                       markup);
    }
    catch (Exception e) {
      out.print("Error trying to print: " + term0);
      e.printStackTrace(System.err);
    }
    out.flush();
  }

  /** Parses and typechecks the string args into a Pred or an Expr.
   *  The result will be null if args contains parse or type errors.
   *  Otherwise it will be a Term.  You can use 'instanceof Pred'
   *  to find out if the result is a predicate or an expression.
   *
   * @param args String containing an expression or predicate
   * @param out  Where to print error and progress messages.
   * @return     The typechecked Pred/Expr, or null if it contained errors.
   * @throws IOException
   * @throws CommandException
   */
  public Term parseTerm(String args, PrintWriter out)
  throws IOException, CommandException
  {
    SectionManager manager = zlive_.getSectionManager();
    String section = zlive_.getCurrentSection();
    Source src = new StringSource(args);
    Markup markup = zlive_.getMarkup();
    src.setMarkup(markup);
    Term term = ParseUtils.parsePred(src, section, manager);
    if (term instanceof ExprPred)
      term = ((ExprPred)term).getExpr();
    List<? extends ErrorAnn> errors =
      TypeCheckUtils.typecheck(term, manager, false, section);
    if (errors.size() > 0) {
      out.println("Error: term contains type errors.");
      //print any errors
      for (ErrorAnn next : errors) {
        out.println(next);
      }
      return null;
    }
    else
      return term;
  }

  /** Same as parseTerm, but insists on the result being an Expr. */
  public Expr parseExpr(String args, PrintWriter out)
  throws IOException, CommandException
  {
    Term result = parseTerm(args, out);
    if (result instanceof Expr)
      return (Expr) result;
    throw new RuntimeException("expression required, not "+args);
  }

  /** Returns the preprocessed form of a term, before evaluation
   *  starts.  This is mostly used for debugging
   */
  public Term unfoldTerm(Term term)
    throws EvalException, UnboundJokerException
  {
    if (term == null)
      return null;
    String sect = zlive_.getCurrentSection();
    if (sect == null) {
      throw new CztException("Must choose a section!");
    }
    return zlive_.getPreprocess().preprocess(sect, term);
  }
}
