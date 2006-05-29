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

package net.sourceforge.czt.parser.z;

import java.io.*;
import java.net.URL;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.z.UnicodeToLatex;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UrlSource;

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
    File tmpUnicodeFile = File.createTempFile("cztLatexMarkup", ".utf8");
    tmpUnicodeFile.deleteOnExit();
    File tmpLatexFile = File.createTempFile("cztLatexMarkup", ".tex");
    tmpLatexFile.deleteOnExit();
    String uniFile = tmpUnicodeFile.getAbsolutePath();
    String latexFile = tmpLatexFile.getAbsolutePath();
    if (url.toString().endsWith(".tex") || url.toString().endsWith(".TEX")) {
      LatexToUnicode.convert(url, uniFile, new Properties());
      String[] args2 = { "-in", uniFile, "-out", latexFile };
      UnicodeToLatex.main(args2);
      return ParseUtils.parse(new FileSource(tmpLatexFile.getAbsolutePath()),
                              manager_);
    }
    else if (url.toString().endsWith(".utf8") ||
             url.toString().endsWith(".UTF8")) {
      Reader in = new InputStreamReader(url.openStream(), "UTF-8");
      Writer writer =
        new OutputStreamWriter(new FileOutputStream(latexFile));
      UnicodeToLatex.run(in, writer);
      writer.close();
      String[] args2 = { "-in", latexFile, "-out", uniFile };
      LatexToUnicode.main(args2);
      return ParseUtils.parse(new FileSource(tmpLatexFile.getAbsolutePath()),
                              manager_);
    }
    return ParseUtils.parse(new UrlSource(url), manager_);
  }
}
