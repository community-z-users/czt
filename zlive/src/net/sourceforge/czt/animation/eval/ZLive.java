/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2005 Mark Utting

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

import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Iterator;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatPred;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.ZNumeral;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;

public class ZLive
{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  /** The name and current version of ZLive */
  public static final String banner =
    "ZLive version 0.2, (C) 2005, Mark Utting";
  
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
  private int givenSetSize_ = Integer.MAX_VALUE;
  
  /** Generates a fresh temporary name. */
  public ZRefName createNewName()
  {
    // This is a temporary debugging aid, to detect some infinite loops.
    // Once we start evaluating larger terms it will need to be removed
    // (or at least the number increased!).
    if (newNameNum == 554) {
      Exception e = new Exception("infinite loop???  See ZLive.createNewName");
      StringWriter w = new StringWriter();
      e.printStackTrace(new PrintWriter(w));
      sLogger.fine("Stack dump: "+w.toString());
    }
    return factory_.createZRefName("tmp"+(newNameNum++));
  }

  /** Recognises the RefNames produced by createNewName. */
  public /*@pure@*/ boolean isNewName(/*@non_null@*/ ZRefName name) {
    String word = name.getWord();
    return word.matches("tmp[0-9]+");
  }

  public ZLive()
  {
    factory_ = new Factory();
    flatten_ = new Flatten(this);
    sectman_ = new SectionManager();
    sectman_.putCommands("zpatt");
    final String name = "ZLiveDefault";
    try {
      Source specSource = new StringSource("\\begin{zsection} "
                                           + "\\SECTION " + name + " "
                                           + "\\parents standard\\_toolkit "
                                           + "\\end{zsection}",
                                           name);
      specSource.setMarkup(Markup.LATEX);
      sectman_.put(new Key(name ,Source.class), specSource);
      // This parses the above specification
      ZSect sec = (ZSect) sectman_.get(new Key(name, ZSect.class));
      setCurrentSection(sec.getName());
    }
    catch (Exception e) {
      System.err.println("ERROR creating " + name + " section: " + e);
      e.printStackTrace();
    }
    try {
        preprocess_ = new Preprocess(sectman_);
        preprocess_.setRules("/preprocess.tex");
    } catch (Exception e) {
      System.err.println("ERROR loading rules from preprocess.tex: " + e);
      e.printStackTrace();
    }
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

  /** Get the current section manager. */
  public SectionManager getSectionManager()
  { return sectman_; }

   /** Set the section manager which will be used during evaluation. */
  //@ requires sm != null;
  public void setSectionManager(SectionManager sm)
  { sectman_ = sm; }

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
  
  public int getGivenSetSize()
  {
    return givenSetSize_;
  }

  /**
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
    sectman_.get(new Key(sectName, ZSect.class));
    sectman_.get(new Key(sectName, SectTypeEnvAnn.class));
    sectName_ = sectName;
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
    sLogger.entering("ZLive","evalPred");
    if (getCurrentSection() == null) {
      throw new CztException("Must choose a section!");
    }
    // preprocess the predicate, to unfold things.
    pred = (Pred) preprocess_.preprocess(getCurrentSection(), pred);
    
    predlist_ = new FlatPredList(this);
    predlist_.addPred(pred);
    Envir env0 = new Envir();
    predlist_.inferBounds(new Bounds());
    Mode m = predlist_.chooseMode(env0);
    if (m == null) {
      final String message =
        "Cannot find mode to evaluate " + pred +
        " (" + printTerm(pred, markup_) + ")";
      throw new EvalException(message);
    }
    predlist_.setMode(m);
    predlist_.startEvaluation();
    Pred result;
    if (predlist_.nextEvaluation())
      result = factory_.createTruePred();
    else
      result = factory_.createFalsePred();
    sLogger.exiting("ZLive","evalPred");
    return result;
  }

  /** Evaluate an Expr.
      This throws some kind of EvalException if expr is too difficult
      to evaluate or contains an undefined expression.
      The input expression must be type checked.
      @param expr  A net.sourceforge.czt.z.ast.Pred object.
      @return      Usually an instance of EvalSet, or some other expr.
  */
  public Expr evalExpr(Expr expr)
    throws EvalException
  {
    sLogger.entering("ZLive","evalExpr");
    if (getCurrentSection() == null) {
      throw new CztException("Must choose a section!");
    }
    // preprocess the expr, to unfold things.
    expr = (Expr) preprocess_.preprocess(getCurrentSection(), expr);
    
    predlist_ = new FlatPredList(this);
    ZRefName resultName = predlist_.addExpr(expr);
    predlist_.inferBounds(new Bounds());
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
    if ( ! predlist_.nextEvaluation())
        throw new CztException("No solution for expression");
    Expr result = predlist_.getOutputEnvir().lookup(resultName);
    sLogger.exiting("ZLive","evalExpr");
    return result;
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
   */
  public void printTerm(PrintWriter out, Term term, Markup markup)
  {
    if (term instanceof NumExpr) {
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

  public static void main(String args[])
  {
    System.out.println(banner);
    System.out.println("To use ZLive from the command line, run TextUI.");
  }
}
