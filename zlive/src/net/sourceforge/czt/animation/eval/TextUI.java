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
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZNumeral;
import net.sourceforge.czt.z.ast.ZSect;

public class TextUI {
  private static Logger LOG 
    = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  protected static ZLive zlive_ = new ZLive();

  /** Get the instance of ZLive that is used for evaluation. */
  public ZLive getZLive()
  {
    return zlive_;
  }
  
  public static void main (String args[])
        throws IOException
  {
    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
    String str;
    System.out.println(ZLive.banner);

    // save log messages into zlive.log, using our human-readable format
    ZFormatter.startLogging("zlive.log", Level.FINEST);

    boolean finished = false;
    while (!finished) {
      System.out.print("zlive> ");
      str = br.readLine();
      str.trim();
      if (str == null || str.equals("quit") || str.equals("exit"))
        finished = true;
      else if (!str.equals("")) {
        String parts[] = str.split(" +",2);
        processCmd(parts[0],parts.length > 1 ? parts[1] : "");
      }
    }
  }
  
  /** Process one input command. */
  public static void processCmd(String cmd, String args)
  {
    PrintWriter output = new PrintWriter(System.out);
    processCmd(cmd, args, output);
    output.flush();   // don't close it, because it may be System.out.
  }

  /** Process one input command and write output to writer. */
  public static void processCmd(String cmd, String args, PrintWriter out) {
    try {
      final SectionManager manager = zlive_.getSectionManager();
       if (cmd.equals("help")) {
         printHelp(out);
       }
       else if (cmd.equals("ver") || cmd.equals("version")) {
         out.println(ZLive.banner);
       } 
       else if (cmd.equals("why")) {
         zlive_.printCode(out);
       }
       else if (cmd.equals("set")) {
         if (args == null || "".equals(args)) {
           out.println("markup = " + zlive_.getMarkup());
           out.println("section = " + zlive_.getCurrentSection());
           out.println("givensetsize = " + zlive_.getGivenSetSize());
         }
         else {
           final String parts[] = args.split(" +", 2);
           final String value = parts.length > 1 ? parts[1] : "";
           if ("markup".equals(parts[0])) {
             zlive_.setMarkup(value);
           }
           else if ("section".equals(parts[0])) {
             zlive_.setCurrentSection(value);
           }
           else if ("givensetsize".equals(parts[0])) {
             zlive_.setGivenSetSize(value);
           }
           else {
             out.println("Unknown setting " + parts[0]);
           }
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
             out.println("Loading section " + sectName);
             manager.get(new Key(sectName, SectTypeEnvAnn.class));
           }
         }
         if (sectName != null) {
           out.println("Setting section to " + sectName);
           zlive_.setCurrentSection(sectName);
         }
       }
       else if (cmd.equals("conjectures")) {
         final String section = zlive_.getCurrentSection();
         if (section != null) {
           ZSect sect = (ZSect) manager.get(new Key(section, ZSect.class));
           for (Para par : sect.getPara())
             if (par instanceof ConjPara) {
               LocAnn loc = (LocAnn) par.getAnn(LocAnn.class);
               if (loc != null) {
                 out.println("Conjecture on line "+loc.getLine());
               }
               try {
                 ConjPara conj = (ConjPara) par;
                 printTerm(out, zlive_.evalPred( conj.getPred() ), zlive_.getMarkup());
                 out.println();
               }
               catch (Exception e) {
                 out.println("Error: "+e);
                 e.printStackTrace(out);
               }
           }
           out.println();
         }
       }
       else if (cmd.equals("env")) {
         final String section = zlive_.getCurrentSection();
         if (section != null) {
           out.println(manager.get(new Key(section, OpTable.class)));
           out.println(manager.get(new Key(section, DefinitionTable.class)));
         }
       }
       else if (cmd.equals("eval") || cmd.equals("evalp")) {
         String section = zlive_.getCurrentSection();
         Source src = new StringSource(args);
         Markup markup = zlive_.getMarkup();
         src.setMarkup(markup);
         Term term = ParseUtils.parsePred(src, section, manager);
         boolean isPred = true;
         if (term instanceof ExprPred) {
           // evaluate just the expression.
           isPred = false;
           term = ((ExprPred)term).getExpr();
         }
         List<? extends ErrorAnn> errors =
           TypeCheckUtils.typecheck(term, manager, false, section);
         if (errors.size() > 0) {
           out.println("Error: term contains type errors.");
           //print any errors
           for (ErrorAnn next : errors) {
             out.println(next);
           }
         }
         else {
           LOG.fine("Starting to evaluate: " + term);
           try
           {
             Term result = null;
             if (isPred)
               result = zlive_.evalPred( (Pred)term );
             else
               result = zlive_.evalExpr( (Expr)term );
             if (result != null)
               printTerm(out, result, markup);
             out.println();
           }
           catch (UndefException ex)
           {
             out.println("Undefined!  " + ex.getMessage());
           }
           catch (EvalException ex)
           {
             out.println();
             out.println("Error: evaluation too difficult/large: "
                       + ex.getMessage()); 
           }
         }
       }
      else {
        out.println("Invalid command.  Try 'help'?");
      }
    }
    catch (SourceLocator.SourceLocatorException e) {
      out.println("Cannot find source for section '" + e.getName() + "'");
    }
    catch (NumberFormatException e) {
      out.println("Error: " + e);
    }
    catch (IllegalArgumentException e) {
      out.println("Error: " + e);
    }
    catch (Exception e) {
      out.println("Error: " + e);
      e.printStackTrace(out);
    }
    out.flush();
  }

  /** Prints help/usage message */
  public static void printHelp(PrintStream out)
  {
    PrintWriter writer = new PrintWriter(out);
    printHelp(writer);
    writer.flush();
  }

  /** Writes help/usage message */
  public static void printHelp(PrintWriter out)
  {
    out.println("\n--------------- ZLive Help ---------------");
    out.println("load file.tex     -- Read a Z specification into ZLive");
    out.println("eval <expr>       -- Evaluate an expression");
    out.println("evalp <pred>      -- Evaluate a predicate (synonym for eval)");
    out.println("why               -- Print out the internal code of the last command");
    out.println("set               -- Print out all settings");
    out.println("set <var> <value> -- Sets <var> to <value>.");
    out.println("version           -- Display the version of ZLive");
    out.println("quit              -- Exit the ZLive program");
    out.println();
    out.flush();
  }

  /** Prints an evaluated expression as a standard text string. 
   */
  public static void printTerm(PrintStream out, Term term, Markup markup)
  {
    PrintWriter writer = new PrintWriter(out);
    printTerm(writer, term, markup);
    writer.flush();
  }

  /** Writes an evaluated expression as a standard text string. 
   */
  public static void printTerm(PrintWriter out, Term term, Markup markup)
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

  public static String printTerm(Term term, Markup markup)
  {
    StringWriter stringWriter = new StringWriter();
    printTerm(new PrintWriter(stringWriter), term, markup);
    return stringWriter.toString();
  }
}
