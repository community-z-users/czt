/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.parser.oz;

import java.io.*;

import java_cup.runtime.Symbol;
import junit.framework.*;

import net.sourceforge.czt.parser.util.AbstractLatexToUnicodeTest;
import net.sourceforge.czt.session.SectionManager;

/**
 * A (JUnit) test class for testing the latex to unicode converter.
 */
public class LatexToUnicodeTest
  extends AbstractLatexToUnicodeTest
{
  SectionManager manager_ = new SectionManager();

  private String lex(String string)
    throws Exception
  {
    LatexToUnicode lexer =
      new LatexToUnicode(new java.io.StringReader(string), manager_);
    lexer.setSource("'" + string + "'");
    StringWriter result = new StringWriter();
    Symbol s = null;
    while ((s = lexer.next_token()).sym != Sym.EOF) {
      result.write((String) s.value);
    }
    result.close();
    return result.toString();
  }

  protected void transforms(String in, String out)
  {
    try {
      String result = lex(in);
      Assert.assertEquals(out, result);
    }
    catch (Exception e) {
      e.printStackTrace();
      fail("Should not throw an Exception");
    }
  }
}
