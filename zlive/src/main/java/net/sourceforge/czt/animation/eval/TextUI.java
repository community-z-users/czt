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
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.flatpred.FlatGivenSet;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.GivenValue;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.ProverUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.SimpleProver;
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
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZNumeral;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zpatt.ast.PredSequent;
import net.sourceforge.czt.zpatt.ast.Rule;
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
  
  /** The current output */
  protected PrintWriter output_;

  /** Get the instance of ZLive that is used for evaluation. */
  public ZLive getZLive()
  {
    return zlive_;
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
      output_.print("zlive> ");
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

  /** Process one input command and write output to writer. */
  public void processCmd(String cmd, String args)
  {
    try {
      final SectionManager manager = zlive_.getSectionManager();
      if (cmd.equals("eval") || cmd.equals("evalp"))
        evalExprPred(args, output_);
      else if (cmd.equals("help")) {
        printHelp(output_);
      }
      else if (cmd.equals("unfold")) {
        Term term = parseTerm(args, output_);
        term = unfoldTerm(term);
        if (term != null)
          output_.println("Term = "+zlive_.printTerm(term));
      }
      else if (cmd.equals("ver") || cmd.equals("version")) {
        output_.println(ZLive.getBanner());
      } 
      else if (cmd.equals("why")) {
        zlive_.printCode(output_);
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
      else if (cmd.equals("load")) {
        Source source = new FileSource(args);
        manager.put(new Key(args, Source.class), source);
        Spec spec = (Spec) manager.get(new Key(args, Spec.class));
        String sectName = null;
        for (Sect sect : spec.getSect()) {
          if (sect instanceof ZSect) {
            sectName = ((ZSect) sect).getName();
            output_.println("Loading section " + sectName);
            Key typekey = new Key(sectName, SectTypeEnvAnn.class);
            /* ignore the result */  manager.get(typekey);
          }
        }
        if (sectName != null) {
          output_.println("Setting section to " + sectName);
          zlive_.setCurrentSection(sectName);
        }
      }
      else if (cmd.equals("reset")) {
        zlive_.reset();
        System.out.println("All specifications cleared...");
      }
      else if (cmd.equals("show")) {
        String sectName = zlive_.getCurrentSection();
        SectTypeEnvAnn types = (SectTypeEnvAnn) manager.get(new Key(sectName, SectTypeEnvAnn.class));
        for (NameSectTypeTriple triple : types.getNameSectTypeTriple()) {
          if (triple.getSect().equals(sectName))
            System.out.println("    "+triple.getZName()+":  "+triple.getType());
        }
      }
      else if (cmd.equals("conjectures")) {
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
      else if (cmd.equals("env")) {
        final String section = zlive_.getCurrentSection();
        if (section != null) {
          output_.println(manager.get(new Key(section, OpTable.class)));
          output_.println(manager.get(new Key(section, DefinitionTable.class)));
        }
      }
      else if (cmd.equals("apply")) {
        if (args == null || "".equals(args)) {
          output_.println("Invalid command.  Try 'help'");
        }
        else {
          final String parts[] = args.split(" +", 2);
          if (parts.length > 1) {
            String section = zlive_.getCurrentSection();
            Source src = new StringSource(parts[1]);
            Markup markup = zlive_.getMarkup();
            src.setMarkup(markup);
            Expr expr = ParseUtils.parseExpr(src, section, manager);
            List<? extends ErrorAnn> errs = TypeCheckUtils.typecheck(expr, manager, false, section);
            if (errs.size() > 0)
              output_.println("Type errors: "+errs);
            RuleTable rules = (RuleTable)
              manager.get(new Key("ZLivePreprocess", RuleTable.class));
            Rule rule = rules.get(parts[0]);
            if (rule == null) {
              output_.println("Cannot find rule " + parts[0]);
            }
            else {
              Factory fact = new Factory(new ProverFactory());
              ProverJokerExpr joker = (ProverJokerExpr)
                 fact.createJokerExpr("_");
              Pred pred = ProverUtils.FACTORY.createEquality(expr, joker);
              PredSequent predSequent =
                ProverUtils.createPredSequent(pred, true);
              SimpleProver prover = new SimpleProver(rules, manager, section);
              if (SimpleProver.apply2(rule, predSequent)) {
                int proveresult = prover.prove(predSequent.getDeduction().getSequent());
                if (proveresult < 0)
                  output_.println(zlive_.printTerm(ProverUtils.removeJoker(joker.boundTo())));                 
                else
                  output_.println("Could not prove antecedent "+proveresult);
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
      }
      else {
        output_.println("Invalid command.  Try 'help'");
      }
    }
    catch (SourceLocator.SourceLocatorException e) {
      output_.println("Cannot find source for section '" + e.getName() + "'");
    }
    catch (NumberFormatException e) {
      // probably an incorrect parameter to the 'set' command.
      output_.println("Error: " + e);
    }
    catch (IllegalArgumentException e) {
      // probably an incorrect parameter to the 'set' command.
      output_.println("Error: " + e);
    }
    catch (Exception e) {
      output_.println("Error: " + e);
      e.printStackTrace(output_);  // TODO: for debugging (remove later)
    }
    output_.flush();
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

  /** Returns the preprocessed form of a term, before evaluation 
   *  starts.  This is mostly used for debugging
   */
  public Term unfoldTerm(Term term)
  throws EvalException
  {
    if (term == null)
      return null;
    String sect = zlive_.getCurrentSection();
    if (sect == null) {
      throw new CztException("Must choose a section!");
    }
    return zlive_.getPreprocess().preprocess(sect, term);
  }

  public void evalExprPred(String args, PrintWriter out)
  throws IOException, CommandException
  {
    Term term = parseTerm(args, out);
    if (term == null)
      return;
    LOG.fine("Starting to evaluate: " + term);
    try
    {
      Term result = null;
      if (term instanceof Pred)
        result = zlive_.evalPred( (Pred)term );
      else
        result = zlive_.evalExpr( (Expr)term );
      if (result != null)
        printTerm(out, result, zlive_.getMarkup());
      out.println();
    }
    catch (UndefException ex)
    {
      out.println("Undefined!  " + ex.getMessage());
      if (ex.getTerm() != null) {
        out.print("    term = ");
        printTerm(out, ex.getTerm(), zlive_.getMarkup());
        out.println();
      }
    }
    catch (EvalException ex)
    {
      out.println();
      out.println("Error: evaluation too difficult/large: "
          + ex.getMessage());
      if (ex.getTerm() != null) {
        out.print("    term = ");
        printTerm(out, ex.getTerm(), zlive_.getMarkup());
        out.println();
      }
    }
  }

  /** Prints the current values of all the ZLive settings. */
  public void printSettings(PrintWriter out)
  {
    out.println("markup       = " + zlive_.getMarkup());
    out.println("section      = " + zlive_.getCurrentSection());
    out.println("givensetsize = " + zlive_.getGivenSetSize());
    out.println("numitersize  = " + RangeSet.getNumIterSize());
    out.println("searchsize   = " + FlatPredList.getSearchSize());
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
    else if ("searchsize".equals(name)) {
        FlatPredList.setSearchSize(value);
      }
    else {
      output_.println("Unknown setting: " + name);
    }
  }

  /** Prints the ZLive help/usage message */
  public void printHelp(PrintWriter out)
  {
    out.println("\n--------------- ZLive Help ---------------");
    out.println("load file.tex     -- Read a Z specification into ZLive");
    out.println("eval <expr>       -- Evaluate an expression");
    out.println("evalp <pred>      -- Evaluate a predicate (synonym for eval)");
    out.println("why               -- Print out the internal code of the last command");
    out.println("set               -- Print out all settings");
    out.println("set <var> <value> -- Sets <var> to <value>.");
    out.println("show              -- Show name & type of defns in current section");
    out.println("version           -- Display the version of ZLive");
    out.println("help              -- Display this help summary");
    out.println("conjectures       -- Evaluate all conjectures in the current section");
    out.println("reset             -- Remove all loaded specifications");
    out.println("quit              -- Exit the ZLive program");
    out.println();
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
   */
  public void printTerm(PrintWriter out, Term term, Markup markup)
  {
    if (term instanceof NumExpr) {
      NumExpr num = (NumExpr) term;
      ZNumeral znum = (ZNumeral) num.getNumeral();
      out.print(znum.getValue());
    }
    else if (term instanceof GivenValue) {
      out.print(((GivenValue)term).getValue());
    }
    else if (term instanceof FlatGivenSet) {
      out.print(((FlatGivenSet)term).getName());
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
          PrintUtils.printLatex(term, out, zlive_.getSectionManager(),
                                zlive_.getCurrentSection());
          out.flush();
          return;
        }
        catch (Exception e) {
          e.printStackTrace(System.err);
        }
      }
      try {
        PrintUtils.printUnicode(term, out, zlive_.getSectionManager());
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

  public String printTerm(Term term, Markup markup)
  {
    StringWriter stringWriter = new StringWriter();
    printTerm(new PrintWriter(stringWriter), term, markup);
    return stringWriter.toString();
  }
}
