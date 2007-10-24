/*
  Copyright (C) 2004, 2005, 2006, 2007 Petra Malik
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.print.z;

import java.io.Writer;
import java.util.Properties;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.WarningManager;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.util.PrettyPrinter;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.util.Section;

/**
 * Utilities for printing Z specifications given as an AST.
 *
 * @author Petra Malik
 */
public final class PrintUtils
{
  /**
   * Do not create instances of this class.
   */
  private PrintUtils()
  {
  }
  
  public static final WarningManager warningManager_ =
    new WarningManager(PrintUtils.class);

  /**
   * Prints a given term (usually a Spec or Sect) in the specified
   * markup to the given writer.  The section information is used to
   * obtain the operator table and latex markup table needed for
   * printing, and should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>
   * and
   * <code>net.sourceforge.czt.parser.util.LatexMarkupTable.class</code>.
   *
   * This method may be used for terms like Spec and Sect that contain
   * a section header so that context information can be obtained from
   * the tree itself.  See {@link
   * #print(Term,Writer,SectionManager,String,Markup)} for
   * writing trees that do not contain context information.
   */
  public static void print(Term term,
                           Writer out,
                           SectionManager sectInfo,
                           Markup markup)
  {
    final String sectionName = Section.STANDARD_TOOLKIT.getName();
    print(term, out, sectInfo, sectionName, markup);
  }

  public static void print(Term term,
                           Writer out,
                           SectionManager sectInfo,
                           String sectName,
                           Markup markup)
  {
    switch (markup) {
    case  LATEX:
      printLatex(term, out, sectInfo, sectName);
      break;
    case  UNICODE:
      printUnicode(term, out, sectInfo, sectName);
      break;
    default:
      String message = "Attempt to print unsupported markup";
      throw new PrintException(message);
    }
  }

  public static void printOldLatex(Term term,
                                   Writer out,
                                   SectionManager sectInfo)
  {
    String sectionName = Section.STANDARD_TOOLKIT.getName();
    printOldLatex(term, out, sectInfo, sectionName);
  }

  /**
   * Prints a given term (usually an Expr or Pred) as latex markup to
   * the given writer.  The name of section (where this term belongs
   * to) and the section information is used to obtain the operator
   * table and latex markup table needed for printing.  The section
   * information should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>
   * and
   * <code>net.sourceforge.czt.parser.util.LatexMarkupTable.class</code>.
   *
   * This method may be used for terms like Expr and Pred that do not
   * contain a section header so that context information cannot be
   * obtained from the tree itself.  See
   * {@link #printLatex(Term,Writer,SectionManager)} for writing trees that do
   * contain context information.
   */
  public static void printLatex(Term term,
                                Writer out,
                                SectionManager sectInfo,
                                String sectionName)
  {
    warningManager_.clear();
    TokenSequence tseq = PrintUtils.toUnicode(term, sectInfo, sectionName,
                                              sectInfo.getProperties());
    ZmlScanner scanner = new ZmlScanner(tseq.iterator());
    Unicode2Latex parser = new Unicode2Latex(prepare(scanner, term));
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      String msg = "An exception occurred while trying to print " +
        "LaTeX markup for term within section " + sectionName;
      throw new PrintException(msg, e);
    }
  }

  public static void printOldLatex(Term term,
                                   Writer out,
                                   SectionManager sectInfo,
                                   String sectionName)
  {
    warningManager_.clear();  
    term.accept(new ToSpiveyZVisitor());
    AstToPrintTreeVisitor toPrintTree =
      new AstToPrintTreeVisitor(sectInfo, warningManager_);
    toPrintTree.setOldZ(true);
    Term tree = toPrintTree(toPrintTree, term, sectionName);
    Properties props = new Properties(sectInfo.getProperties());
    props.setProperty(PrintPropertiesKeys.PROP_Z_EVES, "true");
    ZmlScanner scanner = new ZmlScanner(tree, props);
    Unicode2OldLatex parser = new Unicode2OldLatex(prepare(scanner, term));
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      String msg = "An exception occurred while trying to print " +
        "old (Spivey's) LaTeX markup.";
      throw new PrintException(msg, e);
    }
  }

  /**
   * Prints a given term (usually an Expr or Pred) as unicode to the
   * given writer.  The name of section (where this term belongs to)
   * and the section information is used to obtain the operator table
   * and latex markup table needed for printing.  The section
   * information should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   *
   * This method may be used for terms like Expr and Pred that do not
   * contain a section header so that context information cannot be
   * obtained from the tree itself.  See {@link
   * #printUnicode(Term,Writer,SectionManager)} for writing trees that
   * do contain context information.
   */
  public static void printUnicode(Term term,
                                  Writer out,
                                  SectionManager sectInfo,
                                  String sectionName)
  {
    Properties props = sectInfo.getProperties();
    TokenSequence tseq = toUnicode(term, sectInfo, sectionName, props);
    UnicodePrinter printer = new UnicodePrinter(out);
    printer.printTokenSequence(tseq);
  }

  public static TokenSequence toUnicode(Term term,
                                        SectionManager sectInfo,
                                        String sectionName,
                                        Properties props)
  {
    Term tree = preprocess(term, sectInfo, sectionName);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    tree.accept(precVisitor);
    TokenSequenceVisitor visitor = new TokenSequenceVisitor(props);
    tree.accept(visitor);
    TokenSequence tseq = visitor.getResult();
    int textWidth = textWidth(props);
    if (textWidth > 0) {
      PrettyPrinter prettyPrinter = new PrettyPrinter();
      prettyPrinter.setLineWidth(textWidth);
      prettyPrinter.handleTokenSequence(tseq, 0);
    }
    return tseq;
  }


  public static int textWidth(Properties props)
  {
    String value = props.getProperty(PrintPropertiesKeys.PROP_TXT_WIDTH);
    try {
      return Integer.valueOf(value);
    }
    catch (NumberFormatException e) {
      return -1;
    }
  }

  public static Term preprocess(Term term,
                                SectionManager manager,
                                String section)
    throws PrintException
  {
    AstToPrintTreeVisitor toPrintTree =
      new AstToPrintTreeVisitor(manager, warningManager_);
    return toPrintTree(toPrintTree, term, section);
  }

  public static Term toPrintTree(AstToPrintTreeVisitor toPrintTree,
                                 Term term,
                                 String sectionName)
  {
    try {
      return (Term) toPrintTree.run(term, sectionName);
    }
    catch (CommandException exception) {
      String msg =
        "A command exception occurred while trying to print Unicode markup " +
        "for term within section " + sectionName;
      throw new PrintException(msg, exception);
    }
  }

  private static Scanner prepare(ZmlScanner scanner, Term term)
  {
    Scanner result = scanner;
    if (term instanceof Spec) {
      result = new SectHeadScanner(scanner);
    }
    else if (term instanceof Para) {
      scanner.prepend(new Symbol(Sym.PARA_START));
      scanner.append(new Symbol(Sym.PARA_END));
    }
    else {
      scanner.prepend(new Symbol(Sym.TOKENSEQ));
      scanner.append(new Symbol(Sym.TOKENSEQ));
    }
    return result;
  }
}
