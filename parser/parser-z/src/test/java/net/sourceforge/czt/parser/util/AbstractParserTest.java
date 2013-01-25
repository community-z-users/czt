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

package net.sourceforge.czt.parser.util;

import java.io.*;
import java.net.URL;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.Examples;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.*;
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
  private  SectionManager manager_ = null;

  protected SectionManager getManager()
  {
	  if (manager_ == null)
	  {
		  manager_ = new SectionManager(getDialect());
	  }
	  return manager_;
  }
  
  protected abstract Dialect getDialect();
  
  protected void setUp() throws Exception
  {
    getManager().reset();
    getManager().putCommands(getDialect());
    /*
    // MarkU: Oct 2008
    // Parse standard toolkit once, to avoid doing it in every test.
    // This reduces the ZmlPrinterTest time from 40secs to 25secs,
    // but also adds SectionManager warnings about duplicate keys.
    // So it is probably not worth enabling it for a relatively small gain.

    Key<ZSect> toolkit = new Key<ZSect>("standard_toolkit", ZSect.class);
    if ( ! manager_.isCached(toolkit)) {
      Source source = new UrlSource(getLibFile("standard_toolkit.tex"));
      String name = source.getName();
      manager_.put(new Key<Source>(name, Source.class), source);
      manager_.get(new Key<Spec>(name, Spec.class));
    }
    */
  }

  protected URL getExample(String name)
  {
    return Examples.getExample(name);
  }

  protected URL getTestExample(String name)
  {
    return Examples.getTestExample(name);
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

  public void testConjectureNames()
    throws Exception
  {
    Visitor<Term> visitor = new DeleteNarrVisitor();
    Spec parsedSpec =
      (Spec) parse(getTestExample("conjectures.tex"), getManager()).accept(visitor);
    assertEquals(1, parsedSpec.getSect().size());
    ZSect zsect = (ZSect) parsedSpec.getSect().get(0);
    ConjPara conj1 = null;
    // find first conjecture
    for (Para p : zsect.getZParaList()) {
      if (p instanceof ConjPara) {
        conj1 = (ConjPara) p;
        break;
      }
    }
    assertNotNull(conj1);
    assertNotNull(conj1.getName());
    assertEquals("newline", conj1.getName());
  }

  public void testTest()
    throws Exception
  {
    compare(getTestExample("test.tex"), getTestExample("test.xml"));
  }

  public void testChunqing()
    throws Exception
  {
    compare(getTestExample("chunqing.tex"), getTestExample("chunqing.xml"));
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

  public void testLatexMarkupWithoutNl1()
    throws Exception
  {
    compare(getTestExample("latexMarkupWithoutNl1.tex"),
            getTestExample("latexMarkupWithoutNl1.xml"));
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
  implements TermVisitor<Term>
{
  public Term visitTerm(Term term)
  {
    VisitorUtils.visitTerm(this, term);
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
    if (locAnn != null) locAnn.setLoc(null);
    return null;
  }
}
