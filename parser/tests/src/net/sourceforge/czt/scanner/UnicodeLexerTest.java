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

  private void nextIsDecorword(String string)
    throws java.io.IOException
  {
    Symbol symbol = lexer_.next_token();
    Assert.assertEquals(sym.DECORWORD, symbol.sym);
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

  private void isDecorWord(String string)
    throws java.io.IOException
  {
    lexer_.yyreset(new java.io.StringReader(string));
    nextIsDecorword(string);
    nextIsEof();
  }

  public void testExample7_3_1()
    throws java.io.IOException
  {
    isDecorWord("&+=");
    isDecorWord("x_+_y");
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

    isDecorWord(lambda + "S");
    isDecorWord(delta + "S");
    isDecorWord(exi + cross);
    isDecorWord(exi + "_X");
    isDecorWord(exi + se + "x" + nw);

    lexer_.yyreset(new java.io.StringReader(exi + "S"));
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
    isDecorWord(cross + ":" + mem);
    isDecorWord(se + "x" + nw + ":" + se + "e" + nw);

    lexer_.yyreset(new java.io.StringReader("x:e"));
    nextIsDecorword("x");
    nextIsColon();
    nextIsDecorword("e");
  }
}
