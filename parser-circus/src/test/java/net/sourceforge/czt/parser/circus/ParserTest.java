/*
  Copyright (C) 2004, 2006 Leo Freitas
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

package net.sourceforge.czt.parser.circus;

import java.io.*;
import java.net.URL;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.jaxb.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.*;

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
 
  public void testCircusSimple1()
    throws Exception
  {
    //compareCircus(getCircusTestExample("simple1.tex"),
    //          getCircusTestExample("simple1.xml"));
  }

  public Term parse(URL url, SectionManager manager)
    throws Exception
  {
    return ParseUtils.parse(new UrlSource(url), manager);
  }

  public void compareCircus(URL url, URL zmlURL)
    throws Exception
  {
    JaxbXmlReader reader = new JaxbXmlReader();
    Visitor visitor = new DeleteNarrVisitor();
    Spec zmlSpec = (Spec) reader.read(zmlURL.openStream()).accept(visitor);
    Spec parsedSpec =
      (Spec) parse(url, manager_).accept(visitor);
    visitor = new DeleteMarkupParaVisitor();
    parsedSpec = (Spec) parsedSpec.accept(visitor);
    zmlSpec = (Spec) zmlSpec.accept(visitor);
    JaxbValidator validator = new JaxbValidator();
    Assert.assertTrue(validator.validate(parsedSpec));
    Assert.assertTrue(validator.validate(zmlSpec));
    if (! zmlSpec.equals(parsedSpec)) {
      String message = "For " + url.toString();
      JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
      File expected = File.createTempFile("cztCircusParser", "test.zml");
      Writer out =
        new OutputStreamWriter(new FileOutputStream(expected), "UTF-8");
      xmlWriter.write(zmlSpec, out);
      out.close();
      message += "\nexpected: " + expected.getAbsolutePath();
      File got = File.createTempFile("cztCircusParser", "test.zml");
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
    public Term parse(URL url, SectionManager manager)
      throws Exception
    {
      return ParseUtils.parse(new UrlSource(url), manager);
    }
  }

  public URL getCircusExample(String name)
  {
    URL result = net.sourceforge.czt.zml.Examples.getCircusExample(name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }

  public URL getCircusTestExample(String name)
  {
    URL result = getClass().getResource("/tests/circus/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
}
