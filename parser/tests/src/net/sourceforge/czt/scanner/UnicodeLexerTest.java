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

package net.sourceforge.czt.scanner;

import java.io.*;
import java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.util.ZChar;
import net.sourceforge.czt.util.ZString;

/**
 * A (JUnit) test class for testing the unicode lexer.
 */
public class UnicodeLexerTest extends TestCase
{
  private UnicodeLexer lexer_ =
    new UnicodeLexer(new java.io.StringReader(""));

  public static Test suite()
  {
    return new TestSuite(UnicodeLexerTest.class);
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
    Assert.assertEquals(sym.DECORWORD, symbol.sym);
    Assert.assertEquals(string, symbol.value);
  }

  private void nextIsNumeral(Integer integer)
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.NUMERAL, symbol.sym);
    Assert.assertEquals(integer, symbol.value);
  }

  private void nextIsStroke(String string)
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.STROKE, symbol.sym);
    Assert.assertEquals(string, symbol.value);
  }

  private void nextIsNl()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.NL, symbol.sym);
  }

  private void nextIsZed()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.ZED, symbol.sym);
  }

  private void nextIsEnd()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.END, symbol.sym);
  }

  private void nextIsSch()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.SCH, symbol.sym);
  }

  private void nextIsBar()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.BAR, symbol.sym);
  }

  private void nextIsPower()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.POWER, symbol.sym);
  }

  private void nextIsEquals()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.EQUALS, symbol.sym);
  }

  private void nextIsLsquare()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.LSQUARE, symbol.sym);
  }

  private void nextIsRsquare()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.RSQUARE, symbol.sym);
  }

  private void nextIsExi()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.EXI, symbol.sym);
  }

  private void nextIsColon()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.COLON, symbol.sym);
  }

  private void nextIsComma()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.COMMA, symbol.sym);
  }

  private void nextIsEof()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.EOF, symbol.sym);
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
    String exi = String.valueOf(ZChar.EXI);
    String se = String.valueOf(ZChar.SE);
    String nw = String.valueOf(ZChar.NW);
    String cross = String.valueOf(ZChar.CROSS);
    String delta = String.valueOf(ZChar.DELTA);
    String lambda = String.valueOf(ZChar.LAMBDA);

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
    String cross = String.valueOf(ZChar.CROSS);
    String mem = String.valueOf(ZChar.MEM);
    String se = String.valueOf(ZChar.SE);
    String nw = String.valueOf(ZChar.NW);
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
    nextIsStroke("!");
    nextIsEnd();
    nextIsEof();

    resetLexer(ZString.ZEDCHAR + "x! !" + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x!");
    nextIsStroke("!");
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
    String se = String.valueOf(ZChar.SE);
    String nw = String.valueOf(ZChar.NW);
    String sw = String.valueOf(ZChar.SW);
    String ne = String.valueOf(ZChar.NE);

    resetLexer(ZString.ZEDCHAR + "x" + se + "a" + nw + se + "1" + nw
               + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x" + se + "a" + nw);
    nextIsStroke(se + "1" + nw);
    nextIsEnd();
    nextIsEof();

    resetLexer(ZString.ZEDCHAR + "x" + se + "a" + nw + "?"
               + ZString.ENDCHAR);
    nextIsZed();
    nextIsDecorword("x" + se + "a" + nw);
    nextIsStroke("?");
    nextIsEnd();
    nextIsEof();

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
    String end = String.valueOf(ZChar.ENDCHAR);
    String tutorial = String.valueOf(ZChar.ZEDCHAR) + "[NAME, DATE]" + end;
    tutorial += String.valueOf(ZChar.SCHCHAR) + "BirthdayBook ";
    tutorial += "known:" + String.valueOf(ZChar.POWER) + " NAME" + "\n";
    tutorial += "birthday:NAME" + String.valueOf(ZChar.PFUN) + "DATE";
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
    nextIsDecorword(String.valueOf(ZChar.PFUN));
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
