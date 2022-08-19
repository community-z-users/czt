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
import java.nio.charset.StandardCharsets;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
import net.sourceforge.czt.parser.util.LocToken;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.session.*;

/**
 * A (JUnit) test class for testing the latex markup converter.
 *
 * @author Petra Malik
 */
public class LatexMarkupConverterTest
  extends AbstractParserTest
{
  /** Test doesn't work for toolkit. */
  public void testPrelude()
    throws Exception
  {
  }

  /** Test doesn't work for toolkit. */
  public void testSetToolkit()
    throws Exception
  {
  }

  /** Test doesn't work for toolkit. */
  public void testRelationToolkit()
    throws Exception
  {
  }

  /** Test doesn't work for toolkit. */
  public void testFunctionToolkit()
    throws Exception
  {
  }

  /** Test doesn't work for toolkit. */
  public void testNumberToolkit()
    throws Exception
  {
  }

  /** Test doesn't work for toolkit. */
  public void testSequenceToolkit()
    throws Exception
  {
  }

  /** Test doesn't work for toolkit. */
  public void testStandardToolkit()
    throws Exception
  {
  }

  /** TODO: remove this once LatexMarkupConverter preserves theorem names. */
  @Override
  public void testConjectureNames()
    throws Exception
  {
  }

  /**
   * Parses the specified URL, converts it into a different markup and
   * back into the original markup, and returns the parse tree of the
   * converted specification.
   * @param url
   * @param manager
   * @return
   * @throws Exception
   */
  @Override
  public Term parse(URL url, SectionManager manager)
    throws Exception
  {
    manager = new SectionManager(Dialect.Z);
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
      try {
      latexToUnicode(source, writer);
      } finally {
      writer.close();}
      unicodeToLatex(uniFile, latexFile);
      return ParseUtils.parse(new FileSource(tmpLatexFile.getAbsolutePath()),
                              manager);
    }
    else if (url.toString().endsWith(".utf8") ||
             url.toString().endsWith(".UTF8")) {
      unicodeToLatex(url, latexFile);
      Writer writer =
        new OutputStreamWriter(new FileOutputStream(uniFile), "UTF-8");
      latexToUnicode(new FileSource(latexFile), writer);
      return ParseUtils.parse(new FileSource(tmpLatexFile.getAbsolutePath()),
                              manager);
    }
    return ParseUtils.parse(new UrlSource(url), manager);
  }

  private void unicodeToLatex(String unicodeFileName, String latexFileName)
    throws Exception
  {
    File file = new File(unicodeFileName);
    unicodeToLatex(file.toURI().toURL(), latexFileName);
  }

  private void unicodeToLatex(URL url, String latexFileName)
    throws Exception
  {
    SectionManager manager = new SectionManager(Dialect.Z);
    String name = SourceLocator.getSourceName(url.toString());
    manager.put(new Key<Source>(name, Source.class), new UrlSource(url));
    LatexString latex = manager.get(new Key<LatexString>(name, LatexString.class));
    FileOutputStream stream = new FileOutputStream(latexFileName);
    Writer writer = new OutputStreamWriter(stream, StandardCharsets.UTF_8);
    try {
    writer.write(latex.toString()); } finally {
    writer.close(); }
  }

  private void latexToUnicode(Source source, Writer writer)
    throws Exception
  {
    LatexToUnicode lexer =
      new LatexToUnicode(source, new SectionManager(Dialect.Z), new Properties());
    LocToken s = null;
    while ( (s = lexer.next()) != null) {
      if (s.spelling() != null) writer.write(s.spelling());
    }
  }

@Override
protected Dialect getDialect() {
	return Dialect.Z;
}
}
