/*
  Copyright (C) 2004 Petra Malik
  This file is part of the CZT project: http://czt.sourceforge.net

  The CZT project contains free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as published
  by the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License along
  with CZT; if not, write to the Free Software Foundation, Inc.,
  59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.util;

import java.util.HashMap;
import java.util.Map;

import java_cup.runtime.Scanner;
import java_cup.runtime.Symbol;

import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.ZChar;

/**
 * A latex markup parser that looks like a scanner.
 * Instances of this class are usually used after the Latex2Unicode
 * converter.  It preprocesses the output of the converter and updates
 * the markup function appropriately.  It is possible to use the same
 * markup function in the converter if each markup command is used
 * AFTER it is defined in a markup directive.
 */
public class LatexMarkupParser
  implements Scanner
{
  private static ZFactory factory_ = new ZFactoryImpl();

  /**
   * The latex to unicode scanner that provides the input.
   */
  private LatexScanner scanner_;

  /**
   * Section information.
   */
  private SectionInfo sectInfo_;

  /**
   * The markup function for the current section.
   */
  private LatexMarkupFunction markupFunction_ = null;

  /**
   * All markup functions created so far.
   */
  private Map markupFunctions_ = new HashMap();

  /**
   * Are we just parsing a section header?
   */
  private boolean sectHead_ = false;

  /**
   * The current section name.
   */
  private String sectName_ = null;

  /**
   * The parents of the current section.
   */
  private String parents_ = null;

  /**
   * The token returned by the last call to method next_token.
   */
  private Symbol symbol_ = null;

  private String source_ = null;

  /**
   * Creates a new latex markup parser that uses the scanner provided.
   * The section information should be able to provide information of type
   * <code>net.sourceforge.czt.parser.util. LatexMarkupFunction.class</code>.
   */
  public LatexMarkupParser(LatexScanner scanner,
                           SectionInfo sectInfo)
  {
    scanner_ = scanner;
    sectInfo_ = sectInfo;
  }

  public String getSource()
  {
    return source_;
  }

  public void setSource(String source)
  {
    source_ = source;
  }

  /**
   * Adds the markup function of the given specification
   * to the current markup function.
   *
   * @param parent the name of the parent specification.
   */
  private void addMarkupFunction(String parent)
    throws MarkupException
  {
    if (markupFunction_ == null) {
      markupFunction_ = new LatexMarkupFunction(sectName_);
      markupFunctions_.put(sectName_, markupFunction_);
      scanner_.setMarkupFunction(markupFunction_);
    }
    LatexMarkupFunction markupFunction =
      (LatexMarkupFunction) markupFunctions_.get(parent);
    if (markupFunction == null) {
      markupFunction = (LatexMarkupFunction)
        sectInfo_.getInfo(parent, LatexMarkupFunction.class);
    }
    if (markupFunction != null) {
      markupFunction_.add(markupFunction);
    }
  }

  public Map getMarkupFunctions()
  {
    return markupFunctions_;
  }

  public Symbol next_token()
    throws Exception
  {
    Symbol token = scanner_.next_token();
    if (sectName_ == null &&
        (token.sym == LatexSym.CHAR_MARKUP ||
         token.sym == LatexSym.WORD_MARKUP ||
         token.sym == LatexSym.INWORD_MARKUP ||
         token.sym == LatexSym.PREWORD_MARKUP ||
         token.sym == LatexSym.POSTWORD_MARKUP ||
         token.sym == LatexSym.UNICODE)) {
      // we are parsing an anonymous specification
      sectName_ = "Specification";
      parents_ = "standard_toolkit";
      addMarkupFunction("prelude");
      addMarkupFunction(parents_);
    }
    if (sectHead_) { // we are just parsing a section header
      if (token.sym == LatexSym.END) { // end of section header
        sectName_ = sectName_.trim();
        markupFunction_ = new LatexMarkupFunction(sectName_);
        markupFunctions_.put(sectName_, markupFunction_);
        scanner_.setMarkupFunction(markupFunction_);
        if (! sectName_.equals("prelude")) {
          addMarkupFunction("prelude");
        }
        if (parents_ != null) {
          String[] parents = parents_.split(",");
          for (int i = 0; i < parents.length; i++) {
            String parent = parents[i].trim();
            if (parent != null && ! parent.equals("")) {
              addMarkupFunction(parent);
            }
          }
        }
        sectHead_ = false;
      }
      else if (token.sym == LatexSym.SECTION) { // section token
        // start parsing section name
        sectName_ = "";
      }
      else if (token.sym == LatexSym.PARENTS) { // parents token
        // start parsing parents
        parents_ = "";
      }
      else {
        if (parents_ != null) {
          parents_ += token.value;
        }
        else if (sectName_ != null) {
          sectName_ += token.value;
        }
        else {
          System.err.println("Unexpected token '" + token.value +
                             "' within a section header.");
        }
      }
    }
    else if (token.sym == LatexSym.SECT) { // begin of a section header
      sectHead_ = true;
      parents_ = null;
      sectName_ = null;
    }
    else if (token.sym == LatexSym.CHAR_MARKUP) {
      Directive directive = parseCharMarkupDirective((String) token.value,
                                                     token.left);
      if (directive != null) {
        markupFunction_.add(directive);
      }
      return next_token();
    }
    else if (token.sym == LatexSym.WORD_MARKUP) {
      parseWordMarkup(DirectiveType.NONE, token.left);
    }
    else if (token.sym == LatexSym.INWORD_MARKUP) {
      parseWordMarkup(DirectiveType.IN, token.left);
    }
    else if (token.sym == LatexSym.PREWORD_MARKUP) {
      parseWordMarkup(DirectiveType.PRE, token.left);
    }
    else if (token.sym == LatexSym.POSTWORD_MARKUP) {
      parseWordMarkup(DirectiveType.POST, token.left);
    }
    check(symbol_, token);
    if (token != null && token.value != null) {
      symbol_ = token;
    }
    return token;
  }

  private void check(Symbol t1, Symbol t2)
  {
    final String message = "WARNING: Possible missing hard space at line "
      + t2.left + " column " + t2.right + " in " + source_;
    if (t1 != null && t2 != null) {
      if (t1.sym == LatexSym.UNICODE && t2.sym == LatexSym.UNICODE) {
        String s1 = (String) t1.value;
        String s2 = (String) t2.value;
        if (s1.length() > 0 && s2.length() > 0) {
          char c1 = s1.charAt(s1.length() - 1);
          char c2 = s2.charAt(0);
          final boolean c1IsLetterOrDigit =
            Character.isDigit(c1) || Character.isLetter(c1);
          final boolean c2IsLetterOrDigit =
            Character.isDigit(c2) || Character.isLetter(c2);
          final boolean c1IsDeltaOrXi =
            c1 == ZChar.DELTA || c1 == ZChar.XI;
          final boolean cond =
            c1IsLetterOrDigit && c2IsLetterOrDigit && ! c1IsDeltaOrXi;
          if (cond) {
            System.err.println(message);
          }
        }
      }
    }
  }

  private void parseWordMarkup(DirectiveType type, int line)
    throws Exception
  {
    String name = parseName();
    String latex = parseUnicode();
    Directive directive = factory_.createDirective(name, latex, type);
    directive.getAnns().add(factory_.createLocAnn(null,
                                                  new Integer(line),
                                                  null));
    markupFunction_.add(directive);
  }

  private String parseName()
    throws Exception
  {
    Symbol token = scanner_.next_token();
    if (token.sym == LatexSym.NAME) {
      return (String) token.value;
    }
    System.err.println("Error while parsing markup directive.");
    return null;
  }

  private String parseUnicode()
    throws Exception
  {
    String result = "";
    Symbol token = scanner_.next_token();
    while (token.sym != LatexSym.END_MARKUP) {
      result += token.value;
      token = scanner_.next_token();
    }
    return result;
  }

  public static Directive parseCharMarkupDirective(String directive, int line)
  {
    String[] splitted = directive.split("[ \t]+");
    final int expectedLength = 3;
    if (splitted.length == expectedLength) {
      DirectiveType type = DirectiveType.NONE;
      String name = splitted[1];
      if ("%%Zprechar".equals(splitted[0])) {
        type = DirectiveType.PRE;
      }
      else if ("%%Zpostchar".equals(splitted[0])) {
        type = DirectiveType.POST;
      }
      else if ("%%Zinchar".equals(splitted[0])) {
        type = DirectiveType.IN;
      }

      if (splitted[2].startsWith("U+")) {
        final int beginString = 2;
        final int endString = 6;
        String hexValue = splitted[2].substring(beginString, endString);
        final int hexBase = 16;
        int decimal = Integer.parseInt(hexValue, hexBase);
        // Java 1.4
        Character character = new Character((char) decimal);
        String unicode = character.toString();
        // Java 1.5
        //        char[] chars = Character.toChars(decimal);
        //        String unicode = new String(chars);
        Directive d = factory_.createDirective(name, unicode, type);
        d.getAnns().add(factory_.createLocAnn(null,
                                              new Integer(line),
                                              null));
        return d;
      }
      System.err.println("WARNING: Cannot parse " + directive);
      return null;
    }
    System.err.println("WARNING: Cannot parse " + directive);
    return null;
  }

  public interface LatexScanner
    extends Scanner
  {
    void setMarkupFunction(LatexMarkupFunction markupFunction);
  }
}
