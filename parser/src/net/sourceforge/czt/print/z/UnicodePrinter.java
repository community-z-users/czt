/*
  Copyright (C) 2004, 2005 Petra Malik
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

import java.io.PrintWriter;
import java.io.Writer;
import java.util.Map;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * Print Z specifications in Unicode.
 * This class adds the functionality to print Z tokens in unicode
 * to the PrintWriter class.
 *
 * @author Petra Malik
 */
public class UnicodePrinter
  extends PrintWriter
{
  /**
   * Create a new PrintWriter, without automatic line flushing.
   *
   * @param out a character-output stream.
   */
  public UnicodePrinter(Writer out)
  {
    super(out);
  }

  /**
   * Create a new PrintWriter.
   *
   * @param out a character-output stream.
   * @param autoFlush a boolean; if true, the println() methods
   *                  will flush the output buffer
   */
  public UnicodePrinter(Writer out, boolean autoFlush)
  {
    super(out, autoFlush);
  }

  /**
   * Prints the AX token.
   */
  public void printAX()
  {
    print(ZString.AX);
  }

  /**
   * Prints a DECORWORD.
   */
  public void printDECORWORD(Decorword decorword)
  {
    print(decorword.getName());
  }

  /**
   * Prints the END token.
   */
  public void printEND()
  {
    print(ZString.END);
  }

  /**
   * Prints the GENAX token.
   */
  public void printGENAX()
  {
    print(ZString.GENAX);
  }

  /**
   * Prints the GENSCH token.
   */
  public void printGENSCH()
  {
    print(ZString.GENSCH);
  }

  /**
   * Prints the INSTROKE token.
   */
  public void printINSTROKE()
  {
    print(ZString.INSTROKE);
  }

  /**
   * Prints the LBIND token.
   */
  public void printLBIND()
  {
    print(ZString.LBIND);
  }

  /**
   * Prints the LBRACE token.
   */
  public void printLBRACE()
  {
    print(ZString.LBRACE);
  }

  /**
   * Prints the LDATA token.
   */
  public void printLDATA()
  {
    print(ZString.LDATA);
  }

  /**
   * Prints the LPAREN token.
   */
  public void printLPAREN()
  {
    print(ZString.LPAREN);
  }

  /**
   * Prints the LSQUARE token.
   */
  public void printLSQUARE()
  {
    print(ZString.LSQUARE);
  }

  /**
   * Prints the NEXTSTROKE token.
   */
  public void printNEXTSTROKE()
  {
    print(ZString.PRIME);
  }

  /**
   * Prints a NL token.
   */
  public void printNL()
  {
    print(ZString.NL);
  }

  /**
   * Prints a numeral.
   */
  public void printNUMERAL(Integer value)
  {
    print(value);
  }

  /**
   * Prints the NUMSTROKE token.
   */
  public void printNUMSTROKE(Integer number)
  {
    print(ZString.SE + number + ZString.NW);
  }

  /**
   * Prints the OUTSTROKE token.
   */
  public void printOUTSTROKE()
  {
    print(ZString.OUTSTROKE);
  }

  /**
   * Prints the PARENTS token.
   */
  public void printPARENTS()
  {
    print("parents");
  }

  /**
   * Prints the RBIND token.
   */
  public void printRBIND()
  {
    print(ZString.RBIND);
  }

  /**
   * Prints the RBRACE token.
   */
  public void printRBRACE()
  {
    print(ZString.RBRACE);
  }

  /**
   * Prints the RDATA token.
   */
  public void printRDATA()
  {
    print(ZString.RDATA);
  }

  /**
   * Prints the RPAREN token.
   */
  public void printRPAREN()
  {
    print(ZString.RPAREN);
  }

  /**
   * Prints the RSQUARE token.
   */
  public void printRSQUARE()
  {
    print(ZString.RSQUARE);
  }

  /**
   * Prints the SECTION token.
   */
  public void printSECTION()
  {
    print("section");
  }

  /**
   * Prints the SCH token.
   */
  public void printSCH()
  {
    print(ZString.SCH);
  }

  /**
   * Prints a SPACE.
   */
  public void printSPACE()
  {
    print(ZString.SPACE);
  }

  /**
   * Prints the WHERE token.
   */
  public void printWHERE()
  {
    print(ZString.NL + ZString.VL + ZString.NL);
  }

  /**
   * Prints the ZED token.
   */
  public void printZED()
  {
    print(ZString.ZED);
  }

  /**
   * Prints a token from ZSymbol.
   */
  public void printSymbol(Symbol s)
  {
    assert s.left == ZPrintVisitor.Z;
    switch(s.sym) {
    case(Sym.TEXT):
      print(s.value);
      break;
    case(Sym.ZED):
      printZED();
      break;
    case(Sym.AX):
      printAX();
      break;
    case(Sym.GENAX):
      printGENAX();
      break;
    case(Sym.SCH):
      printSCH();
      break;
    case(Sym.GENSCH):
      printGENSCH();
      break;
    case(Sym.PARENTS):
      printPARENTS();
      break;
    case(Sym.SECTION):
      printSECTION();
      break;
    case(Sym.WHERE):
      printWHERE();
      break;
    case(Sym.END):
      printEND();
      break;
    case(Sym.NL):
      printNL();
      break;
    case(Sym.LPAREN):
      printLPAREN();
      break;
    case(Sym.RPAREN):
      printRPAREN();
      break;
    case(Sym.LSQUARE):
      printLSQUARE();
      break;
    case(Sym.RSQUARE):
      printRSQUARE();
      break;
    case(Sym.LBRACE):
      printLBRACE();
      break;
    case(Sym.RBRACE):
      printRBRACE();
      break;
    case(Sym.LBIND):
      printLBIND();
      break;
    case(Sym.RBIND):
      printRBIND();
      break;
    case(Sym.LDATA):
      printLDATA();
      break;
    case(Sym.RDATA):
      printRDATA();
      break;
    case(Sym.INSTROKE):
      printINSTROKE();
      break;
    case(Sym.OUTSTROKE):
      printOUTSTROKE();
      break;
    case(Sym.NEXTSTROKE):
      printNEXTSTROKE();
      break;
    case(Sym.NUMSTROKE):
      printNUMSTROKE((Integer) s.value);
      break;
    case(Sym.NUMERAL):
      printNUMERAL((Integer) s.value);
      break;
    case(Sym.DECORWORD):
      printDECORWORD((Decorword) s.value);
      break;
    default :
      Map fieldMap = DebugUtils.getFieldMap(Sym.class);
      throw new CztException("Unexpected token (" + s.sym + ", " +
			     fieldMap.get(s.sym) + ", " +
			     s.value + ")");
    }
  }

  /**
   * Print a Z specification.  The token returned by the scanner
   * are simply translated into unicode; no parsing, syntax, or
   * semantic checking is performed.
   *
   * @param scanner a scanner that returns Z token.
   */
  public void printZed(Scanner scanner)
  {
    try {
      Symbol s = null;
      while ( (s = scanner.next_token()).sym != Sym.EOF) {
	printSymbol(s);
        if (s.sym != Sym.TEXT) printSPACE();
      }
    }
    catch (Exception e) {
      throw new CztException(e);
    }
  }
}
