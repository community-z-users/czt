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

import junit.framework.*;

import net.sourceforge.czt.util.ZChar;

/**
 * A (JUnit) test class for testing the latex to unicode converter.
 */
public class Latex2UnicodeTest extends TestCase
{
  private Latex2Unicode lexer_ =
    new Latex2Unicode(new java.io.StringReader(""));

  private StringWriter result_ = new StringWriter();

  private void lex(String string)
    throws java.io.IOException
  {
    result_ = new StringWriter();
    lexer_.setWriter(result_);
    lexer_.yyreset(new java.io.StringReader(string));
    while (lexer_.yylex() != -1) {
    }
  }

  public static Test suite()
  {
    return new TestSuite(Latex2UnicodeTest.class);
  }

  private void transforms(String in, String out)
    throws java.io.IOException
  {
    lex("\\begin{zed}" + in + "\\end{zed}");
    Assert.assertEquals(String.valueOf(ZChar.ZEDCHAR)
                        + out
                        + String.valueOf(ZChar.ENDCHAR),
                        result_.toString());
  }

  public void testPrechar()
    throws java.io.IOException
  {
    transforms("\\power S",
               String.valueOf(ZChar.POWER)
               + String.valueOf(ZChar.SPACE)
               + "S");
    transforms("{\\power}S", String.valueOf(ZChar.POWER) + "S");
               
  }

  public void testInchar()
    throws java.io.IOException
  {
    transforms("\\subseteq",
               String.valueOf(ZChar.SPACE)
               + String.valueOf(ZChar.SUBSETEQ)
               + String.valueOf(ZChar.SPACE));
    transforms("\\subseteq_1",
               String.valueOf(ZChar.SPACE)
               + String.valueOf(ZChar.SUBSETEQ)
               + String.valueOf(ZChar.SE)
               + "1"
               + String.valueOf(ZChar.NW)
               + String.valueOf(ZChar.SPACE));
    transforms("\\subseteq~_1",
               String.valueOf(ZChar.SPACE)
               + String.valueOf(ZChar.SUBSETEQ)
               + String.valueOf(ZChar.SPACE)
               + String.valueOf(ZChar.SE)
               + "1"
               + String.valueOf(ZChar.NW)
               + String.valueOf(ZChar.SPACE));
    transforms("{\\subseteq}", String.valueOf(ZChar.SUBSETEQ));
  }

  public void testGreekLetters()
    throws java.io.IOException
  {
    transforms("\\Delta  S", String.valueOf(ZChar.DELTA) + "S");
    transforms("\\Delta~S",
               String.valueOf(ZChar.DELTA)
               + String.valueOf(ZChar.SPACE)
               + "S");
    transforms("\\lambda x",
               String.valueOf(ZChar.LAMBDA)
               + String.valueOf(ZChar.SPACE)
               + "x");
    transforms("{\\lambda}x", String.valueOf(ZChar.LAMBDA) + "x");
  }

  public void testPlusSign()
    throws java.io.IOException
  {
    transforms("x+y", "x + y");
    transforms("x{+}y", "x+y");
    transforms("x +_1 y",
               "x +"
               + String.valueOf(ZChar.SE)
               + "1"
               + String.valueOf(ZChar.NW)
               + " y");
    transforms("x^+",
               "x"
               + String.valueOf(ZChar.NE)
               + "1"
               + String.valueOf(ZChar.SW));
  }
}
