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
  
public class UnicodeLexerTest extends TestCase
{
  UnicodeLexer lexer_ = new UnicodeLexer(new java.io.StringReader(""));

  public static Test suite() {
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

  private void nextIsEof()
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.EOF, symbol.sym);
  }

  private void isDecorword(String string)
    throws java.io.IOException
  {
    resetLexer(string);
    nextIsDecorword(string);
    nextIsEof();
  }

  public void testExample7_3_1()
    throws java.io.IOException
  {
    isDecorword("&+=");
    isDecorword("x_+_y");
    // TODO: add the others
  }

  public void testExample7_3_2()
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

    resetLexer(exi + "S");
    nextIsExi();
    nextIsDecorword("S");
    nextIsEof();
  }

  public void testExample7_3_3()
    throws java.io.IOException
  {
    String cross = String.valueOf(ZChar.CROSS);
    String mem = String.valueOf(ZChar.MEM);
    String se = String.valueOf(ZChar.SE);
    String nw = String.valueOf(ZChar.NW);
    isDecorword(cross + ":" + mem);
    isDecorword(se + "x" + nw + ":" + se + "e" + nw);

    resetLexer("x:e");
    nextIsDecorword("x");
    nextIsColon();
    nextIsDecorword("e");
  }

  public void testExample7_3_4()
    throws java.io.IOException
  {
    isDecorword("abc");

    resetLexer("a bc");
    nextIsDecorword("a");
    nextIsDecorword("bc");
    nextIsEof();

    isDecorword("a12");

    resetLexer("a 12");
    nextIsDecorword("a");
    nextIsNumeral(new Integer(12));
    nextIsEof();

    isDecorword("x!");

    resetLexer("x !");
    nextIsDecorword("x");
    nextIsStroke("!");
    nextIsEof();

    resetLexer("x! !");
    nextIsDecorword("x!");
    nextIsStroke("!");
    nextIsEof();
  }

  public void testExample7_3_5()
    throws java.io.IOException
  {
    String se = String.valueOf(ZChar.SE);
    String nw = String.valueOf(ZChar.NW);
    String sw = String.valueOf(ZChar.SW);
    String ne = String.valueOf(ZChar.NE);

    resetLexer("x" + se + "a" + nw + se + "1" + nw);
    nextIsDecorword("x" + se + "a" + nw);
    nextIsStroke(se + "1" + nw);
    nextIsEof();

    resetLexer("x" + se + "a" + nw + "?");
    nextIsDecorword("x" + se + "a" + nw);
    nextIsStroke("?");
    nextIsEof();

    resetLexer("x" + ne + "b" + se + "3" + nw + sw);
    nextIsDecorword("x" + ne + "b" + se + "3" + nw + sw);
    nextIsEof();
 }
}
