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

import net.sourceforge.czt.util.ZString;

/**
 * A (JUnit) test class for testing the latex to unicode converter.
 */
public class Latex2UnicodeTest extends AbstractLatexToUnicodeTest
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

  protected void transforms(String in, String out)
  {
    try {
      lex("\\begin{zed}" + in + "\\end{zed}");
      Assert.assertEquals(ZString.ZED + out + ZString.END,
                          result_.toString());
    }
    catch (IOException e) {
      fail("Should not throw an IOException");
    }
  }
}
