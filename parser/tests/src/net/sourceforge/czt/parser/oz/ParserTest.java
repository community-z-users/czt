/*
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
import java.net.URL;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.oz.jaxb.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.*;
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
    suite.addTestSuite(ParserTest.class);
    suite.addTestSuite(ParserExceptionTest.class);
    return suite;
  }

  /**
   * Example test5.tex cannot be parses with the Object Z parser
   * since the keyword "Init" is used as a schema name.
   */
  public void test5Test()
  {
    try {
      parse(getTestExample("test5.tex"), manager_);
      fail("Should throw ParseException");
    }
    catch (ParseException ok) {
      // we want to end up here
    }
    catch (IOException e) {
      fail("Should not throw IOException");
    }
  }

  public void testCC()
  {
    compareOz(getOzExample("CC.tex"),
              getOzExample("CC.xml"));
  }

  public void testDms()
  {
    compareOz(getOzExample("dms.tex"),
              getOzExample("dms.xml"));
  }

  public void testGraph()
  {
    compareOz(getOzExample("graph.tex"),
              getOzExample("graph.xml"));
  }

  public void testMtr()
  {
    compareOz(getOzExample("mtr.tex"),
              getOzExample("mtr.xml"));
  }

  public void testPirate()
  {
    compareOz(getOzExample("pirate.tex"),
              getOzExample("pirate.xml"));
  }

  public void testShunting()
  {
    compareOz(getOzExample("shunting.tex"),
              getOzExample("shunting.xml"));
  }

  public void testTreespec()
  {
    compareOz(getOzExample("treespec.tex"),
              getOzExample("treespec.xml"));
  }

  public void testOzSimple1()
  {
    compareOz(getOzTestExample("simple1.tex"),
              getOzTestExample("simple1.xml"));
  }

  public Term parse(URL url, SectionManager manager)
    throws ParseException, IOException
  {
    return ParseUtils.parse(url, manager);
  }

  public void compareOz(URL url, URL zmlURL)
  {
    try {
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
    catch (Exception e) {
      e.printStackTrace();
      fail("Should not throw exception " + e);
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
      throws ParseException, IOException
    {
      return ParseUtils.parse(url, manager);
    }
  }
}
