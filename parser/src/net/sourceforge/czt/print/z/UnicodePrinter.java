/**
Copyright 2004 Petra Malik
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

import java_cup.runtime.Scanner;
import java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * Print Z specifications in Unicode.
 * This class adds the functionality to print Z specifications
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
   * Print a Z specification.  The token returned by the scanner
   * are simply translated into unicode; no parsing, syntax, or
   * semantic checking is performed.
   *
   * @param scanner a scanner that returns Z token.
   */
  public void printZed(Scanner scanner)
    throws Exception
  {
    Symbol s = null;
    while ( (s = scanner.next_token()).sym != Sym.EOF) {
      switch(s.sym) {
        case(Sym.TEXT):
          print(s.value);
          break;
        case(Sym.ZED):
          print(ZString.ZED);
          break;
        case(Sym.AX):
          print(ZString.AX);
          break;
        case(Sym.GENAX):
          print(ZString.GENAX);
          break;
        case(Sym.SCH):
          print(ZString.SCH);
          break;
        case(Sym.GENSCH):
          print(ZString.GENSCH);
          break;
        case(Sym.ELSE):
          print("else");
          break;
        case(Sym.FALSE):
          print("false");
          break;
        case(Sym.FUNCTION):
          print("function");
          break;
        case(Sym.GENERIC) :
          print("generic");
          break;
        case(Sym.IF):
          print("if");
          break;
        case(Sym.LEFTASSOC):
          print("leftassoc");
          break;
        case(Sym.LET):
          print("let");
          break;
        case(Sym.POWER):
          print(ZString.POWER);
          break;
        case(Sym.PARENTS):
          print("parents");
          break;
        case(Sym.ZPRE):
          print("pre");
          break;
        case(Sym.RELATION):
          print("relation");
          break;
        case(Sym.RIGHTASSOC):
          print("rightassoc");
          break;
        case(Sym.SECTION):
          print("section");
          break;
        case(Sym.THEN):
          print("then");
          break;
        case(Sym.TRUE):
          print("true");
          break;
        case(Sym.COLON):
          print(ZString.COLON);
          break;
        case(Sym.DEFEQUAL):
          print("==");
          break;
        case(Sym.COMMA):
          print(ZString.COMMA);
          break;
        case(Sym.DEFFREE):
          print("::=");
          break;
        case(Sym.BAR):
          print(ZString.VL);
          break;
        case(Sym.ANDALSO):
          print(ZString.AMP);
          break;
        case(Sym.ZHIDE):
          print(ZString.ZHIDE);
          break;
        case(Sym.SLASH):
          print("/");
          break;
        case(Sym.DOT):
          print(ZString.DOT);
          break;
        case(Sym.SEMICOLON):
          print(ZString.SEMICOLON);
          break;
        case(Sym.ARG):
          print(ZString.LL);
          break;
        case(Sym.LISTARG):
          print(",,");
          break;
        case(Sym.EQUALS):
          print("=");
          break;
        case(Sym.CONJECTURE):
          print(ZString.VDASH + "?");
          break;
        case(Sym.ALL):
          print(ZString.ALL);
          break;
        case(Sym.SPOT):
          print(ZString.SPOT);
          break;
        case(Sym.EXI):
          print(ZString.EXI);
          break;
        case(Sym.EXIONE):
          print(ZString.EXI + ZString.SUB1);
          break;
        case(Sym.IFF):
          print(ZString.IFF);
          break;
        case(Sym.IMP):
          print(ZString.IMP);
          break;
        case(Sym.OR):
          print(ZString.OR);
          break;
        case(Sym.AND):
          print(ZString.AND);
          break;
        case(Sym.NOT):
          print(ZString.NOT);
          break;
        case(Sym.MEM):
          print(ZString.MEM);
          break;
        case(Sym.ZPROJ):
          print(ZString.ZPROJ);
          break;
        case(Sym.CROSS):
          print(ZString.CROSS);
          break;
        case(Sym.LAMBDA):
          print(ZString.LAMBDA);
          break;
        case(Sym.MU):
          print(ZString.MU);
          break;
        case(Sym.THETA):
          print(ZString.THETA);
          break;
        case(Sym.ZCOMP):
          print(ZString.ZCOMP);
          break;
        case(Sym.ZPIPE):
          print(ZString.ZPIPE);
          break;
        case(Sym.END):
          print(ZString.END);
          break;
        case(Sym.NL):
          print(ZString.NL);
          break;
        case(Sym.LPAREN):
          print(ZString.LPAREN);
          break;
        case(Sym.RPAREN):
          print(ZString.RPAREN);
          break;
        case(Sym.LSQUARE):
          print(ZString.LSQUARE);
          break;
        case(Sym.RSQUARE):
          print(ZString.RSQUARE);
          break;
        case(Sym.LBRACE):
          print(ZString.LBRACE);
          break;
        case(Sym.RBRACE):
          print(ZString.RBRACE);
          break;
        case(Sym.LBIND):
          print(ZString.LBIND);
          break;
        case(Sym.RBIND):
          print(ZString.RBIND);
          break;
        case(Sym.LDATA):
          print(ZString.LDATA);
          break;
        case(Sym.RDATA):
          print(ZString.RDATA);
          break;
        case(Sym.INSTROKE):
          print(ZString.INSTROKE);
          break;
        case(Sym.OUTSTROKE):
          print(ZString.OUTSTROKE);
          break;
        case(Sym.NEXTSTROKE):
          print(ZString.PRIME);
          break;
        case(Sym.NUMSTROKE):
          print(ZString.SE + s.value + ZString.NW);
          break;
        case(Sym.NUMERAL):
          print(s.value);
          break;
        case(Sym.DECORWORD):
          print(s.value);
          break;
        default :
          break;
      }
      if (s.sym != Sym.TEXT) print(ZString.SPACE);
    }
  }
}
