/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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
import java.util.Properties;

import junit.framework.*;

import net.sourceforge.czt.parser.util.AbstractLatexToUnicodeTest;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.session.*;

/**
 * A (JUnit) test class for testing the latex to unicode converter.
 */
public class LatexToUnicodeTest
  extends AbstractLatexToUnicodeTest
{
  private static SectionManager manager_ = new SectionManager(Dialect.OZ);

  private String lex(String string)
    throws Exception
  {
    manager_.reset();
    LatexToUnicode lexer =
      new LatexToUnicode(new StringSource(string, "'" + string + "'"),
                         manager_,
                         new Properties());
    StringWriter result = new StringWriter();
    Token token = null;
    while ((token = lexer.next()) != null) {
      result.write(token.spelling());
    }
    result.close();
    return result.toString();
  }

  protected void transforms(String in, String out)
    throws Exception
  {
    String result = lex(in);
    Assert.assertEquals(out, result);
  }
}
