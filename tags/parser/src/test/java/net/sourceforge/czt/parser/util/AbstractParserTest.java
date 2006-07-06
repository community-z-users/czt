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

package net.sourceforge.czt.parser.util;

import java.io.*;
import java.net.URL;
import net.sourceforge.czt.java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.Examples;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.*;
import net.sourceforge.czt.z.util.DeleteMarkupParaVisitor;
import net.sourceforge.czt.z.util.DeleteNarrVisitor;
import net.sourceforge.czt.z.visitor.*;

/**
 * A (JUnit) test class for testing the parser.
 *
 * @author Petra Malik
 */
public abstract class AbstractParserTest
  extends TestCase
{
  protected static SectionManager manager_ = new SectionManager();

  protected void setUp()
  {
    manager_.reset();
  }

  protected URL getExample(String name)
  {
    return Examples.getExample(name);
  }

  protected URL getOzExample(String name)
  {
    return Examples.getOzExample(name);
  }

  protected URL getTestExample(String name)
  {
    return Examples.getTestExample(name);
  }

  protected URL getOzTestExample(String name)
  {
    return Examples.getOzTestExample(name);
  }

  public void testPrelude()
    throws Exception
  {
    compare(getLibFile("prelude.tex"),
            getLibFile("prelude.xml"));
  }

  public void testSetToolkit()
    throws Exception
  {
    compare(getLibFile("set_toolkit.tex"),
            getLibFile("set_toolkit.xml"));
  }

  public void testRelationToolkit()
    throws Exception
  {
    compare(getLibFile("relation_toolkit.tex"),
            getLibFile("relation_toolkit.xml"));
  }

  public void testFunctionToolkit()
    throws Exception
  {
    compare(getLibFile("function_toolkit.tex"),
            getLibFile("function_toolkit.xml"));
  }

  public void testNumberToolkit()
    throws Exception
  {
    compare(getLibFile("number_toolkit.tex"),
            getLibFile("number_toolkit.xml"));
  }

  public void testSequenceToolkit()
    throws Exception
  {
    compare(getLibFile("sequence_toolkit.tex"),
            getLibFile("sequence_toolkit.xml"));
  }

  public void testStandardToolkit()
    throws Exception
  {
    compare(getLibFile("standard_toolkit.tex"),
            getLibFile("standard_toolkit.xml"));
  }

  public void testLatexBirthdaybookTest()
    throws Exception
  {
    compare(getExample("birthdaybook.tex"),
            getExample("birthdaybook.xml"));
  }

  public void testUtf8BirthdaybookTest()
    throws Exception
  {
    compare(getExample("birthdaybook.utf8"),
            getExample("birthdaybook.xml"));
  }

  public void testUtf16BirthdaybookTest()
    throws Exception
  {
    compare(getExample("birthdaybook.utf16"),
            getExample("birthdaybook.xml"));
  }

  public void testOptemp()
    throws Exception
  {
    compare(getExample("optemp.tex"),
            getExample("optemp.xml"));
  }

  public void testBuffer()
    throws Exception
  {
    compare(getExample("buffer.tex"),
            getExample("buffer.xml"));
  }

  public void testSched()
    throws Exception
  {
    compare(getExample("Sched.tex"),
            getExample("Sched.xml"));
  }

  public void testConjectures()
    throws Exception
  {
    compare(getTestExample("conjectures.tex"),
            getTestExample("conjectures.xml"));
  }

  public void testCase()
    throws Exception
  {
    compare(getTestExample("case.tex"), getTestExample("case.xml"));
  }

  public void testSuccess2Test()
    throws Exception
  {
    compare(getTestExample("success2.tex"), getTestExample("success2.xml"));
  }

  public void testSuccess3Test()
    throws Exception
  {
    compare(getTestExample("success3.tex"), getTestExample("success3.xml"));
  }

  public void testSuccess4Test()
    throws Exception
  {
    compare(getTestExample("success4.tex"), getTestExample("success4.xml"));
  }

  public void testTest()
    throws Exception
  {
    compare(getTestExample("test.tex"), getTestExample("test.xml"));
  }

  public void test1Test()
    throws Exception
  {
    compare(getTestExample("test1.tex"), getTestExample("test1.xml"));
  }

  public void test2Test()
    throws Exception
  {
    compare(getTestExample("test2.tex"), getTestExample("test2.xml"));
  }

  public void test3Test()
    throws Exception
  {
    compare(getTestExample("test3.tex"), getTestExample("test3.xml"));
  }

  public void test4Test()
    throws Exception
  {
    compare(getTestExample("test4.tex"), getTestExample("test4.xml"));
  }

  public void test5Test()
    throws Exception
  {
    compare(getTestExample("test5.tex"), getTestExample("test5.xml"));
  }

  public void test6Test()
    throws Exception
  {
    compare(getTestExample("test6.tex"), getTestExample("test6.xml"));
  }

  public void test7Test()
    throws Exception
  {
    compare(getTestExample("test7.tex"), getTestExample("test7.xml"));
  }

  public void test8Test()
    throws Exception
  {
    compare(getTestExample("test8.tex"), getTestExample("test8.xml"));
  }

  public void test9Test()
    throws Exception
  {
    compare(getTestExample("test9.tex"), getTestExample("test9.xml"));
  }

  public void test10Test()
    throws Exception
  {
    compare(getTestExample("test10.tex"), getTestExample("test10.xml"));
  }

  public void testTesting()
    throws Exception
  {
    compare(getTestExample("testing.tex"), getTestExample("testing.xml"));
  }

  public void testTwosects1()
    throws Exception
  {
    compare(getTestExample("twosects1.tex"), getTestExample("twosects1.xml"));
  }

  public void testNote4()
    throws Exception
  {
    compare(getTestExample("note4inZStd8dot4.tex"),
            getTestExample("note4inZStd8dot4.xml"));
  }

  public void testOpNameInDecl()
    throws Exception
  {
    compare(getTestExample("testOpNameInDecl.tex"),
            getTestExample("testOpNameInDecl.xml"));
  }

  public void testAnimateFreetypes()
    throws Exception
  {
    compare(getTestExample("animate_freetypes.tex"),
            getTestExample("animate_freetypes.xml"));
  }

  public void testAnimateSets()
    throws Exception
  {
    compare(getTestExample("animate_sets.tex"),
            getTestExample("animate_sets.xml"));
  }

  public void testAnimateInts()
    throws Exception
  {
    compare(getTestExample("animate_ints.tex"),
            getTestExample("animate_ints.xml"));
  }

  public void testAnimateMisc()
    throws Exception
  {
    compare(getTestExample("animate_misc.tex"),
            getTestExample("animate_misc.xml"));
  }

  public void testAnimateRelations()
    throws Exception
  {
    compare(getTestExample("animate_relations.tex"),
            getTestExample("animate_relations.xml"));
  }

  public void testAnimateSchemas()
    throws Exception
  {
    compare(getTestExample("animate_schemas.tex"),
            getTestExample("animate_schemas.xml"));
  }

  public void testAnimateScope()
    throws Exception
  {
    compare(getTestExample("animate_scope.tex"),
            getTestExample("animate_scope.xml"));
  }

  public void testAnimateSequences()
    throws Exception
  {
    compare(getTestExample("animate_sequences.tex"),
            getTestExample("animate_sequences.xml"));
  }

  public void testLatexMarkupWithoutNl1()
    throws Exception
  {
    compare(getTestExample("latexMarkupWithoutNl1.tex"),
            getTestExample("latexMarkupWithoutNl1.xml"));
  }

  public void testLatexMarkupWithoutNl2()
    throws Exception
  {
    compare(getTestExample("latexMarkupWithoutNl2.tex"),
            getTestExample("latexMarkupWithoutNl2.xml"));
  }

  private URL getLibFile(String filename)
  {
    return SectionManager.class.getResource("/lib/" + filename);
  }

  public abstract Term parse(URL url, SectionManager manager)
    throws Exception;

  public void compare(URL url, URL zmlURL)
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
      DeleteLocVisitor delLocVisitor = new DeleteLocVisitor();
      zmlSpec.accept(delLocVisitor);
      parsedSpec.accept(delLocVisitor);
      String message = "For " + url.toString();
      JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
      File expected = File.createTempFile("cztParser", "test.zml");
      Writer out =
        new OutputStreamWriter(new FileOutputStream(expected), "UTF-8");
      xmlWriter.write(zmlSpec, out);
      out.close();
      message += " \nexpected: " + expected.getAbsolutePath();
      File got = File.createTempFile("cztParser", "test.zml");
      out = new OutputStreamWriter(new FileOutputStream(got), "UTF-8");
      xmlWriter.write(parsedSpec, out);
      out.close();
      message += " \nbut was:" + got.getAbsolutePath();
      fail(message);
    }
  }
}

class DeleteLocVisitor
  implements TermVisitor
{
  public Object visitTerm(Term term)
  {
    VisitorUtils.visitTerm(this, term);
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
    if (locAnn != null) locAnn.setLoc(null);
    return null;
  }
}
