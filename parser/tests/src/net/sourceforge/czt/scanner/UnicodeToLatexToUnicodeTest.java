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

/**
 * A (junit) test case for testing whether a unicode sequence
 * is lexed the same as the unicode sequence obtained by transforming
 * the former one into latex and back into unicode.
 *
 * @author Petra Malik
 */
public class UnicodeToLatexToUnicodeTest
  extends TestCase
{
  public static Test suite()
  {
    return new TestSuite(UnicodeToLatexToUnicodeTest.class);
  }

  public void testAllUnicodeFiles()
  {
    final String filename = "blubb.utf8";
    try {
      InputStream stream = new FileInputStream(filename);
      InputStreamReader reader = new InputStreamReader(stream, "UTF-8");
      Unicode2Latex u2l = new Unicode2Latex(new UnicodeLexer(reader));
      final File texTemp = File.createTempFile("CztParserTest-", ".tex");
      texTemp.deleteOnExit();
      FileOutputStream outstream = new FileOutputStream(texTemp);
      Writer writer = new OutputStreamWriter(outstream);
      u2l.setWriter(writer);
      u2l.parse();
      writer.close();
      outstream.close();

      reader = new InputStreamReader(new FileInputStream(texTemp));
      LatexToUnicode l2u = new LatexToUnicode(reader);

      final File utf8Temp = File.createTempFile("CztParserTest-", ".utf8");
      //      utf8Temp.deleteOnExit();
      outstream = new FileOutputStream(utf8Temp);
      writer = new OutputStreamWriter(outstream, "UTF-8");
      l2u.Input(writer);
      writer.close();
      outstream.close();

      FileInputStream filestream = new FileInputStream(filename);
      UnicodeLexer lexer1 =
        new UnicodeLexer(new InputStreamReader(filestream, "UTF-8"));
      filestream = new FileInputStream(utf8Temp);
      UnicodeLexer lexer2 =
        new UnicodeLexer(new InputStreamReader(filestream, "UTF-8"));

      Symbol symbol1;
      while ((symbol1 = lexer1.next_token()).sym != sym.EOF) {
        Symbol symbol2 = lexer2.next_token();
        Assert.assertTrue(symbol1.sym == symbol2.sym);
      }
      Assert.assertTrue(lexer2.next_token().sym == sym.EOF);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}
