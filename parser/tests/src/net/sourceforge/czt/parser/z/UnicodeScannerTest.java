/**
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.parser.z;

import java.io.*;
import java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.z.util.ZString;

/**
 * A (JUnit) test class for testing the unicode lexer.
 *
 * @author Petra Malik
 */
public class UnicodeScannerTest extends TestCase
{
  private UnicodeScanner lexer_ =
    new UnicodeScanner(new java.io.StringReader(""));

  public static Test suite()
  {
    return new TestSuite(UnicodeScannerTest.class);
  }

  private void resetLexer(String string)
    throws java.io.IOException
  {
    lexer_.yyreset(new java.io.StringReader(string));
  }

  private void nextIsDecorword(String string)
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.DECORWORD, symbol.sym);
    Assert.assertEquals(string, symbol.value);
  }

  private void nextIsNumeral(Integer integer)
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.NUMERAL, symbol.sym);
    Assert.assertEquals(integer, symbol.value);
  }

  private void nextIsInStroke()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.INSTROKE, symbol.sym);
  }

  private void nextIsOutStroke()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.OUTSTROKE, symbol.sym);
  }

  private void nextIsNumStroke(Integer num)
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.NUMSTROKE, symbol.sym);
    Assert.assertEquals(num, symbol.value);
  }

  private void nextIsNl()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.NL, symbol.sym);
  }

  private void nextIsZed()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.ZED, symbol.sym);
  }

  private void nextIsEnd()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.END, symbol.sym);
  }

  private void nextIsSch()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.SCH, symbol.sym);
  }

  private void nextIsBar()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.BAR, symbol.sym);
  }

  private void nextIsPower()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.POWER, symbol.sym);
  }

  private void nextIsEquals()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.EQUALS, symbol.sym);
  }

  private void nextIsLsquare()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.LSQUARE, symbol.sym);
  }

  private void nextIsRsquare()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.RSQUARE, symbol.sym);
  }

  private void nextIsExi()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.EXI, symbol.sym);
  }

  private void nextIsColon()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.COLON, symbol.sym);
  }

  private void nextIsComma()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.COMMA, symbol.sym);
  }

  private void nextIsEof()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.EOF, symbol.sym);
  }

  private void isDecorword(String string)
    throws java.io.IOException
  {
    resetLexer(ZString.ZEDCHAR + string + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword(string);
    nextIsEnd();
    nextIsEof();
  }

  private void isKeywordElse(String string)
    throws java.io.IOException
  {
    resetLexer(ZString.ZEDCHAR + string + ZString.ENDCHAR);
    nextIsZed();
    Assert.assertEquals(Sym.ELSE, lexer_.next_token().sym);
    nextIsEnd();
    nextIsEof();
  }

  public void testKeywords()
    throws java.io.IOException
  {
    isKeywordElse("else");
    isKeywordElse("   else   ");
    isDecorword("elser");
  }

  /**
   * Example 1 from Z Standard (Working draft 2.7)
   * chapter 7.3.
   */
  public void testExample1()
    throws java.io.IOException
  {
    isDecorword("&+=");
    isDecorword("x_+_y");
    // TODO: add the others
  }

  /**
   * Example 2 from Z Standard (Working draft 2.7)
   * chapter 7.3.
   */
  public void testExample2()
    throws java.io.IOException
  {
    String exi = ZString.EXI;
    String se = ZString.SE;
    String nw = ZString.NW;
    String cross = ZString.CROSS;
    String delta = ZString.DELTA;
    String lambda = ZString.LAMBDA;

    isDecorword(lambda + "S");
    isDecorword(delta + "S");
    isDecorword(exi + cross);
    isDecorword(exi + "_X");
    isDecorword(exi + se + "x" + nw);

    resetLexer(ZString.ZEDCHAR + exi + "S" + ZString.ENDCHAR);
    nextIsZed();
    nextIsExi();
    nextIsDecorword("S");
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 3 from Z Standard (Working draft 2.7)
   * chapter 7.3.
   */
  public void testExample3()
    throws java.io.IOException
  {
    String cross = ZString.CROSS;
    String mem = ZString.MEM;
    String se = ZString.SE;
    String nw = ZString.NW;
    isDecorword(cross + ":" + mem);
    isDecorword(se + "x" + nw + ":" + se + "e" + nw);

    resetLexer(ZString.ZEDCHAR + "x:e" + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x");
    nextIsColon();
    nextIsDecorword("e");
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 4 from Z Standard (Working draft 2.7)
   * chapter 7.3.
   */
  public void testExample4()
    throws java.io.IOException
  {
    isDecorword("abc");

    resetLexer(ZString.ZEDCHAR + "a bc" + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("a");
    nextIsDecorword("bc");
    nextIsEnd();
    nextIsEof();

    isDecorword("a12");

    resetLexer(ZString.ZEDCHAR + "a 12" + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("a");
    nextIsNumeral(new Integer(12));
    nextIsEnd();
    nextIsEof();

    isDecorword("x!");

    resetLexer(ZString.ZEDCHAR + "x !" + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x");
    nextIsOutStroke();
    nextIsEnd();
    nextIsEof();

    resetLexer(ZString.ZEDCHAR + "x! !" + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x!");
    nextIsOutStroke();
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 5 from Z Standard (Working draft 2.7)
   * chapter 7.3.
   */
  public void testExample5()
    throws java.io.IOException
  {
    String se = ZString.SE;
    String nw = ZString.NW;
    String sw = ZString.SW;
    String ne = ZString.NE;

    /* These tests fails since the scanner is not fully conform
       to the scanning phase described in the standard.
    resetLexer(ZString.ZEDCHAR + "x" + se + "a" + nw + se + "1" + nw
               + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x" + se + "a" + nw);
    nextIsNumStroke(new Integer(1));
    nextIsEnd();
    nextIsEof();

    resetLexer(ZString.ZEDCHAR + "x" + se + "a" + nw + "?"
               + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x" + se + "a" + nw);
    nextIsInStroke();
    nextIsEnd();
    nextIsEof();
    */

    resetLexer(ZString.ZEDCHAR + "x" + ne + "b" + se + "3" + nw + sw
               + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x" + ne + "b" + se + "3" + nw + sw);
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Tutorial example (chapter D.3.2)
   * from Z Standard (Working draft 2.7).
   */
  public void testTutorial()
    throws java.io.IOException
  {
    String end = ZString.END;
    String tutorial = ZString.ZED + "[NAME, DATE]" + end;
    tutorial += ZString.SCH + "BirthdayBook ";
    tutorial += "known:" + ZString.POWER + " NAME" + ZString.NLCHAR;
    tutorial += "birthday:NAME" + ZString.PFUN + "DATE";
    tutorial += "|";
    tutorial += "known = dom birthday";
    tutorial += end;

    resetLexer(tutorial);

    nextIsZed();
    nextIsLsquare();
    nextIsDecorword("NAME");
    nextIsComma();
    nextIsDecorword("DATE");
    nextIsRsquare();
    nextIsEnd();

    nextIsSch();
    nextIsDecorword("BirthdayBook");

    nextIsDecorword("known");
    nextIsColon();
    nextIsPower();
    nextIsDecorword("NAME");
    nextIsNl();

    nextIsDecorword("birthday");
    nextIsColon();
    nextIsDecorword("NAME");
    nextIsDecorword(ZString.PFUN);
    nextIsDecorword("DATE");

    nextIsBar();

    nextIsDecorword("known");
    nextIsEquals();
    nextIsDecorword("dom");
    nextIsDecorword("birthday");

    nextIsEnd();
    nextIsEof();
  }
}
