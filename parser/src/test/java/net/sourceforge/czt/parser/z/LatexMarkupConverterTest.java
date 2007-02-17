/*
  Copyright (C) 2004, 2005, 2006, 2007 Petra Malik
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
import java.net.URL;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
import net.sourceforge.czt.parser.util.LocToken;
import net.sourceforge.czt.print.z.UnicodeToLatex;
import net.sourceforge.czt.session.*;

/**
 * A (JUnit) test class for testing the latex markup converter.
 *
 * @author Petra Malik
 */
public class LatexMarkupConverterTest
  extends AbstractParserTest
{
  /**
   * Parses the specified URL, converts it into a different markup and
   * back into the original markup, and returns the parse tree of the
   * converted specification.
   */
  public Term parse(URL url, SectionManager manager)
    throws Exception
  {
    manager = new SectionManager();
    File tmpUnicodeFile = File.createTempFile("cztLatexMarkup", ".utf8");
    tmpUnicodeFile.deleteOnExit();
    File tmpLatexFile = File.createTempFile("cztLatexMarkup", ".tex");
    tmpLatexFile.deleteOnExit();
    final String uniFile = tmpUnicodeFile.getAbsolutePath();
    final String latexFile = tmpLatexFile.getAbsolutePath();
    if (url.toString().endsWith(".tex") || url.toString().endsWith(".TEX")) {
      final Source source = new UrlSource(url);
      final Writer writer =
        new OutputStreamWriter(new FileOutputStream(uniFile), "UTF-8");
      latexToUnicode(source, writer);
      writer.close();
      String[] args2 = { "-in", uniFile, "-out", latexFile };
      UnicodeToLatex.main(args2);
      return ParseUtils.parse(new FileSource(tmpLatexFile.getAbsolutePath()),
                              manager);
    }
    else if (url.toString().endsWith(".utf8") ||
             url.toString().endsWith(".UTF8")) {
      Reader in = new InputStreamReader(url.openStream(), "UTF-8");
      Writer writer =
        new OutputStreamWriter(new FileOutputStream(latexFile));
      UnicodeToLatex.run(in, writer);
      writer.close();
      writer =
        new OutputStreamWriter(new FileOutputStream(uniFile), "UTF-8");
      latexToUnicode(new FileSource(latexFile), writer);
      return ParseUtils.parse(new FileSource(tmpLatexFile.getAbsolutePath()),
                              manager);
    }
    return ParseUtils.parse(new UrlSource(url), manager);
  }

  private void latexToUnicode(Source source, Writer writer)
    throws Exception
  {
    LatexToUnicode lexer = new LatexToUnicode(source, new SectionManager(), new Properties());
    LocToken s = null;
    while ( (s = lexer.next()) != null) {
      if (s.spelling() != null) writer.write(s.spelling());
    }
  }
}
