/**
Copyright 2003 Mark Utting
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

import net.sourceforge.czt.parser.oz.ParseUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.*;

/**
 * A (JUnit) test class for testing the parser.
 * Currently, it is only testing the Object Z parser.
 *
 * @author Petra Malik
 */
public class ParserTest extends TestCase
{
  ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

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

  public void testCompareTest()
  {
    compare("z/test.tex", "z/test.xml");
  }

  public void compare(String latexFile, String zmlFile)
  {
    try {
      JaxbXmlReader reader = new JaxbXmlReader();
      Spec zmlSpec = (Spec) reader.read(new File(zmlFile));
      Spec latexSpec = (Spec) ParseUtils.parseLatexFile(latexFile);
      JaxbValidator validator = new JaxbValidator();
      Assert.assertTrue(validator.validate(latexSpec));
      Assert.assertTrue(validator.validate(zmlSpec));
      if (! zmlSpec.equals(latexSpec)) {
        JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
        File tmpFile = File.createTempFile("czt.parser", "test");
        Writer out = new FileWriter(tmpFile);
        String message = "For " + latexFile + "\nexpected: " + zmlFile;
        xmlWriter.write(latexSpec, out);
        out.close();
        message += " but was:" + tmpFile;
        fail(message);
      }
    }
    catch (Exception e) {
      fail("Should not throw exception " + e);
    }
  }
}
