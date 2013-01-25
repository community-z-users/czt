/*
  Copyright (C) 2004, 2006, 2007 Petra Malik
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
import java.net.URL;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.oz.jaxb.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.*;
import net.sourceforge.czt.zml.Resources;

/**
 * A (JUnit) test class for testing the Z parser.
 *
 * @author Petra Malik
 */
public class ParserTest
  extends AbstractParserTest
{
  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    /* fails at the moment
    suite.addTestSuite(ParserTest.class);
    suite.addTestSuite(ParserExceptionTest.class);
    */
    return suite;
  }

  /**
   * Example test5.tex cannot be parses with the Object Z parser
   * since the keyword "Init" is used as a schema name.
   */
  public void test5Test()
    throws Exception
  {
    try {
      Term term = parse(getTestExample("test5.tex"), getManager());
      // A return value of null is also acceptable
      if (term == null) return;
      fail("Should throw ParseException");
    }
    catch (ParseException ok) {
      // we want to end up here
    }
  }

  public void testCC()
    throws Exception
  {
    compareOz(getOzExample("CC.tex"),
              getOzExample("CC.xml"));
  }

  public void testDms()
    throws Exception
  {
    compareOz(getOzExample("dms.tex"),
              getOzExample("dms.xml"));
  }

  public void testGraph()
    throws Exception
  {
    compareOz(getOzExample("graph.tex"),
              getOzExample("graph.xml"));
  }

  public void testMtr()
    throws Exception
  {
    compareOz(getOzExample("mtr.tex"),
              getOzExample("mtr.xml"));
  }

  public void testPirate()
    throws Exception
  {
    compareOz(getOzExample("pirate.tex"),
              getOzExample("pirate.xml"));
  }

  public void testShunting()
    throws Exception
  {
    compareOz(getOzExample("shunting.tex"),
              getOzExample("shunting.xml"));
  }

  public void testTreespec()
    throws Exception
  {
    compareOz(getOzExample("treespec.tex"),
              getOzExample("treespec.xml"));
  }

  public void testOzSimple1()
    throws Exception
  {
    compareOz(getOzTestExample("simple1.tex"),
              getOzTestExample("simple1.xml"));
  }

  public Term parse(URL url, SectionManager manager)
    throws Exception
  {
    return ParseUtils.parse(new UrlSource(url), manager);
  }

  public void compareOz(URL url, URL zmlURL)
    throws Exception
  {
    JaxbXmlReader reader = new JaxbXmlReader();
    Visitor<Term> visitor = new DeleteNarrVisitor();
    InputStream zmlStream = zmlURL.openStream();
    Term zmlTerm;
    try {
      zmlTerm = reader.read(zmlStream);
    } finally {
      zmlStream.close();
    }
    Spec zmlSpec = (Spec) zmlTerm.accept(visitor);
    Spec parsedSpec =
      (Spec) parse(url, getManager()).accept(visitor);
    visitor = new DeleteMarkupParaVisitor();
    parsedSpec = (Spec) parsedSpec.accept(visitor);
    zmlSpec = (Spec) zmlSpec.accept(visitor);
    if (! zmlSpec.equals(parsedSpec)) {
      String message = "For " + url.toString();
      JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
      File expected = File.createTempFile("cztParser", "test.zml");
      Writer out =
        new OutputStreamWriter(new FileOutputStream(expected), "UTF-8");
      xmlWriter.write(zmlSpec, out);
      out.close();
      message += "\nexpected: " + expected.getAbsolutePath();
      File got = File.createTempFile("cztParser", "test.zml");
      out = new OutputStreamWriter(new FileOutputStream(got), "UTF-8");
      xmlWriter.write(parsedSpec, out);
      out.close();
      message += "\nbut was:" + got.getAbsolutePath();
      fail(message);
    }
  }

  /**
   * A (JUnit) test class for testing the parser.
   * This class contains tests where the parser is supposed to fail,
   * i.e. to throw an exception.
   *
   * @author Petra Malik
   */
  public static class ParserExceptionTest
    extends AbstractParserFailTest
  {
	protected Dialect getDialect() { return Dialect.OZ; }
    public Term parse(URL url, SectionManager manager)
      throws Exception
    {
      return ParseUtils.parse(new UrlSource(url), manager);
    }
  }

  public URL getOzExample(String name)
  {
    URL result = Resources.getOzExample(name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }

  public URL getOzTestExample(String name)
  {
    URL result = getClass().getResource("/tests/oz/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }

@Override
protected Dialect getDialect() {
	
	return Dialect.OZ;
}
}
