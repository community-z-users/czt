/*
  Copyright (C) 2003, 2004, 2005, 2006 Petra Malik
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

import java.math.BigInteger;
import java.util.Properties;
import java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.LocInt;
import net.sourceforge.czt.session.*;

import static net.sourceforge.czt.z.util.ZString.*;

/**
 * A (JUnit) test class for testing the unicode lexer.
 *
 * @author Petra Malik
 */
public class UnicodeScannerTest
  extends TestCase
{
  private UnicodeScanner lexer_;

  private void resetLexer(String string)
    throws Exception
  {
    final String name = "UnicodeScannerTest" + string.hashCode();
    lexer_ = new UnicodeScanner(new StringSource(string, name),
                                new Properties());
  }

  private void nextIsDecorword(String string)
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertTrue(Sym.DECORWORD == symbol.sym ||
                      Sym.DECLWORD == symbol.sym);
    Assert.assertEquals(string, ((Decorword) symbol.value).getName());
  }

  private void nextIsNumeral(int value)
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.NUMERAL, symbol.sym);
    BigInteger foundValue = ((LocInt) symbol.value).getValue();
    Assert.assertEquals(0, BigInteger.valueOf(value).compareTo(foundValue));
  }

  //private void nextIsInStroke()
 //   throws Exception
  //{
  //  Symbol symbol = lexer_.next_token();
  //  Assert.assertEquals(Sym.INSTROKE, symbol.sym);
  //}

  private void nextIsOutStroke()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.OUTSTROKE, symbol.sym);
  }

 // private void nextIsNumStroke(int num)
  //  throws Exception
  //{
   // Symbol symbol = lexer_.next_token();
  //  Assert.assertEquals(Sym.NUMSTROKE, symbol.sym);
  //  BigInteger foundValue = ((LocInt) symbol.value).getValue();
  //  Assert.assertEquals(0, BigInteger.valueOf(num).compareTo(foundValue));
 // }

  private void nextIsNl()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.NL, symbol.sym);
  }

  private void nextIsZed()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.ZED, symbol.sym);
  }

  private void nextIsEnd()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.END, symbol.sym);
  }

  private void nextIsSch()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.SCH, symbol.sym);
  }

  private void nextIsBar()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.BAR, symbol.sym);
  }

  private void nextIsPower()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.POWER, symbol.sym);
  }

  private void nextIsEquals()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.EQUALS, symbol.sym);
  }

  private void nextIsLsquare()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.LSQUARE, symbol.sym);
  }

  private void nextIsRsquare()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.RSQUARE, symbol.sym);
  }

  private void nextIsExi()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.EXI, symbol.sym);
  }

  private void nextIsColon()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.COLON, symbol.sym);
  }

  private void nextIsComma()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.COMMA, symbol.sym);
  }

  private void nextIsEof()
    throws Exception
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(Sym.EOF, symbol.sym);
  }

  private void isDecorword(String string)
    throws Exception
  {
    resetLexer(ZEDCHAR + string + ENDCHAR);
    nextIsZed();
    nextIsDecorword(string);
    nextIsEnd();
    nextIsEof();
  }

  private void isKeywordElse(String string)
    throws Exception
  {
    resetLexer(ZEDCHAR + string + ENDCHAR);
    nextIsZed();
    Assert.assertEquals(Sym.ELSE, lexer_.next_token().sym);
    nextIsEnd();
    nextIsEof();
  }

  public void testKeywords()
    throws Exception
  {
    isKeywordElse("else");
    isKeywordElse("   else   ");
    isDecorword("elser");
  }

  public void testArithmos()
    throws Exception
  {
    isDecorword(ARITHMOS);
    resetLexer(ZED + ARITHMOS + COMMA + END);
    nextIsZed();
    nextIsDecorword(ARITHMOS);
    Assert.assertEquals(Sym.COMMA, lexer_.next_token().sym);
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 1 from Z Standard chapter 7.3.
   */
  public void testExample1()
    throws Exception
  {
    isDecorword("&+=");
    isDecorword("x_+_y");
    isDecorword("x" + SE + "x" + NW + "y");
    isDecorword("x" + NE + "x" + SW + "y");
    isDecorword("x" + NE + "x" + SW + NE + "x" + SW + "y");
    resetLexer(ZED + "x+y" + END);
    nextIsZed();
    nextIsDecorword("x");
    nextIsDecorword("+");
    nextIsDecorword("y");
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 2 from Z Standard chapter 7.3.
   */
  public void testExample2()
    throws Exception
  {
    isDecorword(LAMBDA + "S");
    isDecorword(DELTA + "S");
    isDecorword(EXI + CROSS);
    isDecorword(EXI + "_X");
    isDecorword(EXI + SE + "x" + NW);

    resetLexer(ZEDCHAR + EXI + "S" + ENDCHAR);
    nextIsZed();
    nextIsExi();
    nextIsDecorword("S");
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 4 from Z Standard chapter 7.3.
   * (Example 3 has been deleted by the Technical Corrigendum)
   */
  public void testExample4()
    throws Exception
  {
    isDecorword("abc");

    resetLexer(ZEDCHAR + "a bc" + ENDCHAR);
    nextIsZed();
    nextIsDecorword("a");
    nextIsDecorword("bc");
    nextIsEnd();
    nextIsEof();

    isDecorword("a12");

    resetLexer(ZEDCHAR + "a 12" + ENDCHAR);
    nextIsZed();
    nextIsDecorword("a");
    final int twelve = 12;
    nextIsNumeral(twelve);
    nextIsEnd();
    nextIsEof();

    isDecorword("x!");

    resetLexer(ZEDCHAR + "x !" + ENDCHAR);
    nextIsZed();
    nextIsDecorword("x");
    nextIsOutStroke();
    nextIsEnd();
    nextIsEof();

    resetLexer(ZEDCHAR + "x! !" + ENDCHAR);
    nextIsZed();
    nextIsDecorword("x!");
    nextIsOutStroke();
    nextIsEnd();
    nextIsEof();
  }

  /**
   * Example 5 from Z Standard chapter 7.3.
   */
  public void testExample5()
    throws Exception
  {
    isDecorword("x" + SE + "a" + NW + SE + "1" + NW);
    isDecorword("x" + SE + "a" + NW + "?");
    isDecorword("x" + SE + "1" + NW + SE + "a" + NW);
    isDecorword("x" + NE + "b" + SE + "3" + NW + SW);
  }

  /**
   * Tutorial example (chapter D.3.2) from Z Standard.
   */
  public void testTutorial()
    throws Exception
  {
    String tutorial = ZED + "[NAME, DATE]" + END;
    tutorial += SCH + "BirthdayBook ";
    tutorial += "known:" + POWER + " NAME" + NLCHAR;
    tutorial += "birthday:NAME" + PFUN + "DATE";
    tutorial += "|";
    tutorial += "known = dom birthday";
    tutorial += END;

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
    nextIsDecorword(PFUN);
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
