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
import java.util.logging.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.parser.util.ParseException;

public class TextUI {
  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  protected static ZLive zlive_ = new ZLive();

  /** Markup used when no setting has been provided. */
  protected static Markup defaultMarkup = Markup.LATEX;
  
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
      if (str == null || str.equals("quit") || str.equals("exit"))
        finished = true;
      else if (!str.equals("")) {
        String parts[] = str.split(" ",2);
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
           for (String s : zlive_.propertyNames()) {
             out.println(s + " = " + zlive_.getProperty(s));
           }
         }
         else {
           String parts[] = args.split(" ", 2);
           zlive_.setProperty(parts[0], parts.length > 1 ? parts[1] : "");
         }
       }
       else if (cmd.equals("unset")) {
         zlive_.unsetProperty(args);
       }
       else if (cmd.equals("eval") || cmd.equals("evalp")) {
         SectionManager manager = zlive_.getSectionManager();
         String section = zlive_.getCurrentSection();
         Source src = new StringSource(args);
         Markup markup = defaultMarkup;
         String markupProp = zlive_.getProperty(ZLive.PROP_MARKUP);
         if (Markup.UNICODE.toString().equalsIgnoreCase(markupProp)) {
           markup = Markup.UNICODE;
         }
         src.setMarkup(markup);
         Term term = ParseUtils.parsePred(src, null, manager);
         boolean isPred = true;
         if (term instanceof ExprPred) {
           // evaluate just the expression.
           isPred = false;
           term = ((ExprPred)term).getExpr();
         }
         List<? extends ErrorAnn> errors = TypeCheckUtils.typecheck(term, 
             manager, false, section);
         if (errors.size() > 0) {
           out.println("Error: term contains type errors.");
           //print any errors
           for (ErrorAnn next : errors) {
             out.println(next);
           }
         }
         else {
           out.println("DEBUG: evaluating " + term);
           Term result = null;
           try
           {
             if (isPred)
               result = zlive_.evalPred( (Pred)term );
             else
               result = zlive_.evalExpr( (Expr)term );
           }
           catch (UndefException ex)
           {
             out.print("Undefined!  " + ex.getMessage());
           }
           catch (EvalException ex)
           {
             out.print("Error: evaluation too difficult/large: "
                       + ex.getMessage()); 
           }
           if (result != null)
             printTerm(out, result, markup);
           out.println();
           out.flush();
         }
       }
      else {
        out.println("Invalid command.  Try 'help'?");
      }
    }
    catch (Exception e) {
      out.println("Error: " + e);
      e.printStackTrace(out);
    }
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
    out.println("eval <expr>       -- Evaluate an expression");
    out.println("evalp <pred>      -- Evaluate a predicate (synonym for eval)");
    out.println("why               -- Print out the internal code of the last command");
    out.println("set               -- Print out all settings");
    out.println("set <var> <value> -- Sets <var> to <value>.");
    out.println("version           -- Display the version of ZLive");
    out.println("quit              -- Exit the ZLive program");
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
    else if (term instanceof EvalSet) {
      EvalSet set = (EvalSet) term;
      out.print("{ ");
      Iterator<Expr> i = set.members();
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
          PrintUtils.printLatex(term, out, zlive_.getSectionManager());
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
}
