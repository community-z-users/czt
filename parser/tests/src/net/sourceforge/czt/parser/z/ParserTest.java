/**
Copyright (C) 2003, 2004 Petra Malik
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
import java_cup.runtime.*;

import junit.framework.*;

import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.parser.util.Settings;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.*;
import net.sourceforge.czt.z.util.DeleteNarrVisitor;

/**
 * A (JUnit) test class for testing the parser.
 *
 * @author Petra Malik
 */
public class ParserTest extends TestCase
{
  ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  SectionManager manager_ = new SectionManager();

  public static Test suite()
  {
    return new TestSuite(ParserTest.class);
  }

  private java.util.List getPara(Spec spec)
  {
    java.util.List result = new java.util.Vector();
    java.util.List sects = spec.getSect();
    for (java.util.Iterator iter = sects.iterator(); iter.hasNext();) {
      Sect sect = (Sect) iter.next();
      if (sect instanceof ZSect) {
        result.addAll(((ZSect) sect).getPara());
      }
    }
    return result;
  }

  protected String getCztHome()
  {
    return Settings.getCztHome();
  }

  protected String getExample(String name)
  {
    return getCztHome() + "/zml/examples/z/" + name;
  }

  protected String getTestExample(String name)
  {
    return getCztHome() + "/parser/tests/z/" + name;
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

  /** Not working for some reason I do not understand
  public void test5Test()
  {
    compare(getTestExample("test5.tex"), getTestExample("test5.xml"));
  }
  */

  public void test7Test()
  {
    compare(getTestExample("test7.tex"), getTestExample("test7.xml"));
  }

  public void compare(String filename, String zmlFile)
  {
    try {
      JaxbXmlReader reader = new JaxbXmlReader();
      DeleteNarrVisitor visitor = new DeleteNarrVisitor();
      File zml = new File(zmlFile);
      Spec zmlSpec = (Spec) reader.read(zml).accept(visitor);
      Spec parsedSpec =
        (Spec) ParseUtils.parse(filename, manager_).accept(visitor);
      JaxbValidator validator = new JaxbValidator();
      Assert.assertTrue(validator.validate(parsedSpec));
      Assert.assertTrue(validator.validate(zmlSpec));
      if (! zmlSpec.equals(parsedSpec)) {
        JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
        File tmpFile = File.createTempFile("cztParser", "test.zml");
        Writer out = new FileWriter(tmpFile);
        File file = new File(filename);
        String message = "For " + file.getAbsolutePath();
        message += "\nexpected: " + zml.getAbsolutePath();
        xmlWriter.write(parsedSpec, out);
        out.close();
        message += "\nbut was:" + tmpFile.getAbsolutePath();
        fail(message);
      }
    }
    catch (Exception e) {
      fail("Should not throw exception " + e);
    }
  }
}
