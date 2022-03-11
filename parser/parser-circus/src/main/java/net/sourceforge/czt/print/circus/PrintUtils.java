/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

package net.sourceforge.czt.print.circus;

import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import java_cup.runtime.Symbol;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.z.PrecedenceParenAnnVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;

/**
 * Utilities for printing Circus specifications given as an AST.
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
  
  public static final WarningManager warningManager_ = new WarningManager(PrintUtils.class);

//  /**
//   * Prints a given term (usually a Spec or Sect) in the specified
//   * markup to the given writer.  The section information is used to
//   * obtain the operator table and latex markup table needed for
//   * printing, and should therefore be able to provide information of
//   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>
//   * and
//   * <code>net.sourceforge.czt.parser.util.LatexMarkupTable.class</code>.
//   *
//   * This method may be used for terms like Spec and Sect that contain
//   * a section header so that context information can be obtained from
//   * the tree itself.  See {@link
//   * #print(Term,Writer,SectionManager,String,Markup)} for
//   * writing trees that do not contain context information.
//   */
//  public static void print(Term term,
//                           Writer out,
//                           SectionManager sectInfo,
//                           Markup markup)
//  {    
//    print(term, out, sectInfo, CircusUtils.CIRCUS_TOOLKIT, markup);
//  }
//
//  public static void print(Term term,
//                           Writer out,
//                           SectionManager sectInfo,
//                           String sectName,
//                           Markup markup)
//  {
//    switch (markup) {
//    case  LATEX:
//      new LatexPrinterCommand().printLatex(term, out, sectInfo, sectName);
//      break;
//    case  UNICODE:
//      new UnicodePrinterCommand().printUnicode(term, out, sectInfo, sectName);
//      break;
//    default:
//      String message = "Attempt to print unsupported markup";
//      throw new PrintException(message);
//    }
//  }

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
   * #print(Term,Writer,SectionInfo,String,Markup)} for
   * writing trees that do not contain context information.
   */
  public static void print(Term term,
                           Writer out,
                           SectionInfo sectInfo,
                           Markup markup)
  {
    if (markup == Markup.LATEX) {
      printLatex(term, out, sectInfo);
    }
    else if (markup == Markup.UNICODE) {
      printUnicode(term, out, sectInfo);
    }
    else {
      String message = "Attempt to print unsupported markup";
      throw new UnsupportedOperationException(message);
    }
  }

  public static void print(Term term,
                           Writer out,
                           SectionInfo sectInfo,
                           String sectName,
                           Markup markup)
  {
    if (markup == Markup.LATEX) {
      printLatex(term, out, sectInfo, sectName);
    }
    else if (markup == Markup.UNICODE) {
      printUnicode(term, out, sectInfo, sectName);
    }
    else {
      String message = "Attempt to print unsupported markup";
      throw new UnsupportedOperationException(message);
    }
  }
  
  private static void transformWarningMap(Map<String, Map<Class<?>, List<String>>> to,
      Class<?> with, Map<String, List<String>> from) {
      for(Map.Entry<String, List<String>> entry : from.entrySet()) {                              
          // if there is a key from from, then there must be warnings
          String fromKey = entry.getKey();
          Map<Class<?>, List<String>> toValue;
          
          // either create new entry for sect fromKey or retrieve an old one
          if (to.containsKey(fromKey)) {
            toValue = to.get(fromKey);            
          } else {
            toValue = new HashMap<Class<?>, List<String>>();
            to.put(fromKey, toValue);
          }
          
          assert toValue != null;
          List<String> toWarnings;
          if (toValue.containsKey(with)) {
              toWarnings = toValue.get(with);
          } else {
              toWarnings = new ArrayList<String>(entry.getValue().size());
              toValue.put(with, toWarnings);
          }          
          toWarnings.addAll(entry.getValue());
      }
  }
      

  /**
   * Prints a given term (usually a Spec or Sect) as latex markup to
   * the given writer.  The section information is used to obtain the
   * operator table and latex markup table needed for printing, and
   * should therefore be able to provide information of type
   * <code>net.sourceforge.czt.parser.util.OpTable.class</code> and
   * <code>net.sourceforge.czt.parser.util.LatexMarkupTable.class</code>.
   *
   * This method may be used for terms like Spec and Sect that contain
   * a section header so that context information can be obtained from
   * the tree itself.  See {@link
   * #printLatex(Term,Writer,SectionInfo,String)} for
   * writing trees that do not contain context information.
   */
  public static void printLatex(Term term, Writer out, SectionInfo sectInfo)
  {
    Map<String, Map<Class<?>, List<String>>> warnings = 
        new TreeMap<String, Map<Class<?>, List<String>>>();
    
    warningManager_.clear();
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo, warningManager_);    
    Term tree = term.accept(toPrintTree);    
    
    transformWarningMap(warnings, toPrintTree.getClass(), warningManager_.getZSectWarnings());        
    
    warningManager_.clear();
    //System.out.println("02: CREATING ZML SCANNER FOR TRAVERSED PTV");
    ZmlScanner scanner = new ZmlScanner(sectInfo, tree,((SectionManager)sectInfo).getProperties(), warningManager_);
    transformWarningMap(warnings, scanner.getClass(), warningManager_.getZSectWarnings());        
        
    //System.out.println("03: CREATING UNICODE->LATEX PARSER FOR ZML SCANNER");
    Unicode2Latex parser = new Unicode2Latex(scanner);
    parser.setSectionInfo(sectInfo);
    //System.out.println("04: CREATING UNICODE PRINTER FOR GIVEN FILE WRITER");
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      //System.out.println("05: ABOUT TO PARSE FOR PRINTING USING UNICODE->LATEX PARSER");    
      parser.parse();
      //System.out.println("06: PARSING FOR PRINTING COMPLETE; CHECKING WARNINGS");          
    }
    catch (Exception e) { 
      //System.out.println("07: EXCEPTION OCCURRED WIHTIN PRINT-LATEX METHOD");
      e.printStackTrace();
      throw new CztException(e);
    }
    if (!warnings.isEmpty()) {
        System.out.println(warnings);
    }

    toPrintTree = null;
    tree = null;
    scanner = null;
    parser = null;
    printer = null;
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
   * {@link #printLatex(Term,Writer,SectionInfo)} for writing trees that do
   * contain context information.
   */
  public static void printLatex(Term term,
                                Writer out,
                                SectionInfo sectInfo,
                                String sectionName)
  {
    warningManager_.clear();  
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo, warningManager_);
    Term tree;
    try {
      tree = toPrintTree.run(term, sectionName);
    }
    catch (CommandException exception) {
      throw new CztException(exception);
    }
    ZmlScanner scanner = new ZmlScanner(sectInfo, tree, ((SectionManager)sectInfo).getProperties(), warningManager_);
    scanner.prepend(new Symbol(Sym.TOKENSEQ));
    scanner.append(new Symbol(Sym.TOKENSEQ));
    Unicode2Latex parser = new Unicode2Latex(scanner);
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      throw new CztException(e);
    }

    toPrintTree = null;
    tree = null;
    scanner = null;
    parser = null;
    printer = null;
  }

  /**
   * Prints a given term (usually a Spec or Sect) as unicode to the
   * given writer.  The section information is used to obtain the
   * operator table and latex markup table needed for printing, and
   * should therefore be able to provide information of type
   * <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   *
   * This method may be used for terms like Spec and Sect that contain
   * a section header so that context information can be obtained from
   * the tree itself.  See
   * {@link #printUnicode(Term,Writer,SectionInfo,String)} for writing trees
   * that do not contain context information.
   */
  public static void printUnicode(Term term,
                                  Writer out,
                                  SectionInfo sectInfo)
  {
    warningManager_.clear();  
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo, warningManager_);
    Term tree = term.accept(toPrintTree);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    tree.accept(precVisitor);
    UnicodePrinter printer = new UnicodePrinter(out);
    CircusPrintVisitor visitor = new CircusPrintVisitor(sectInfo, printer, warningManager_);
    tree.accept(visitor);
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
   * obtained from the tree itself.  See
   * {@link #printUnicode(Term,Writer,SectionInfo)} for writing trees that do
   * contain context information.
   */
  public static void printUnicode(Term term,
                                  Writer out,
                                  SectionInfo sectInfo,
                                  String sectionName)
  {
    warningManager_.clear();  
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo, warningManager_);
    Term tree; 
    try {
      tree = toPrintTree.run(term, sectionName);
    }
    catch (CommandException exception) {
      throw new CztException(exception);
    }
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    tree.accept(precVisitor);
    UnicodePrinter printer = new UnicodePrinter(out);
    CircusPrintVisitor visitor = new CircusPrintVisitor(sectInfo, printer, warningManager_);
    tree.accept(visitor);
  }
}
