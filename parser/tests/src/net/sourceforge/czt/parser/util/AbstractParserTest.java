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

package net.sourceforge.czt.parser.util;

import java.io.*;
import java.net.URL;
import java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.Examples;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z.util.DeleteMarkupParaVisitor;
import net.sourceforge.czt.z.util.DeleteNarrVisitor;

/**
 * A (JUnit) test class for testing the parser.
 *
 * @author Petra Malik
 */
public abstract class AbstractParserTest
  extends TestCase
{
  protected SectionManager manager_ = new SectionManager();

  protected URL getExample(String name)
  {
    return Examples.getExample(name);
  }

  protected URL getTestExample(String name)
  {
    return Examples.getTestExample(name);
  }

  public void testPrelude()
  {
    compare(manager_.getLibFile("prelude.tex"),
            manager_.getLibFile("prelude.xml"));
  }

  public void testSetToolkit()
  {
    compare(manager_.getLibFile("set_toolkit.tex"),
            manager_.getLibFile("set_toolkit.xml"));
  }

  public void testRelationToolkit()
  {
    compare(manager_.getLibFile("relation_toolkit.tex"),
            manager_.getLibFile("relation_toolkit.xml"));
  }

  public void testFunctionToolkit()
  {
    compare(manager_.getLibFile("function_toolkit.tex"),
            manager_.getLibFile("function_toolkit.xml"));
  }

  public void testNumberToolkit()
  {
    compare(manager_.getLibFile("number_toolkit.tex"),
            manager_.getLibFile("number_toolkit.xml"));
  }

  public void testSequenceToolkit()
  {
    compare(manager_.getLibFile("sequence_toolkit.tex"),
            manager_.getLibFile("sequence_toolkit.xml"));
  }

  public void testStandardToolkit()
  {
    compare(manager_.getLibFile("standard_toolkit.tex"),
            manager_.getLibFile("standard_toolkit.xml"));
  }

  public void testLatexBirthdaybookTest()
  {
    compare(getExample("birthdaybook.tex"),
            getExample("birthdaybook.xml"));
  }

  public void testUtf8BirthdaybookTest()
  {
    final String cztHome = System.getProperty("czt.home");
    compare(getExample("birthdaybook.utf8"),
            getExample("birthdaybook.xml"));
  }

  public void testUtf16BirthdaybookTest()
  {
    final String cztHome = System.getProperty("czt.home");
    compare(getExample("birthdaybook.utf16"),
            getExample("birthdaybook.xml"));
  }

  public void testSuccess2Test()
  {
    compare(getTestExample("success2.tex"), getTestExample("success2.xml"));
  }

  public void testSuccess3Test()
  {
    compare(getTestExample("success3.tex"), getTestExample("success3.xml"));
  }

  public void testSuccess4Test()
  {
    compare(getTestExample("success4.tex"), getTestExample("success4.xml"));
  }

  public void testTest()
  {
    compare(getTestExample("test.tex"), getTestExample("test.xml"));
  }

  public void test1Test()
  {
    compare(getTestExample("test1.tex"), getTestExample("test1.xml"));
  }

  public void test2Test()
  {
    compare(getTestExample("test2.tex"), getTestExample("test2.xml"));
  }

  public void test3Test()
  {
    compare(getTestExample("test3.tex"), getTestExample("test3.xml"));
  }

  public void test4Test()
  {
    compare(getTestExample("test4.tex"), getTestExample("test4.xml"));
  }

  public void test5Test()
  {
    compare(getTestExample("test5.tex"), getTestExample("test5.xml"));
  }

  public void test7Test()
  {
    compare(getTestExample("test7.tex"), getTestExample("test7.xml"));
  }

  public void testAnimateFreetypes()
  {
    compare(getTestExample("animate_freetypes.tex"),
            getTestExample("animate_freetypes.xml"));
  }

  public void testAnimateSets()
  {
    compare(getTestExample("animate_sets.tex"),
            getTestExample("animate_sets.xml"));
  }

  public void testAnimateInts()
  {
    compare(getTestExample("animate_ints.tex"),
            getTestExample("animate_ints.xml"));
  }

  public void testAnimateMisc()
  {
    compare(getTestExample("animate_misc.tex"),
            getTestExample("animate_misc.xml"));
  }

  public void testAnimateRelations()
  {
    compare(getTestExample("animate_relations.tex"),
            getTestExample("animate_relations.xml"));
  }

  public abstract Term parse(URL url, SectionManager manager)
    throws ParseException, IOException;

  public void compare(URL url, URL zmlURL)
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
}
