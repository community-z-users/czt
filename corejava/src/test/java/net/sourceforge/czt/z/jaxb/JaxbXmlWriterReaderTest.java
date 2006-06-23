/*
  Copyright 2004, 2006 Mark Utting
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

package net.sourceforge.czt.z.jaxb;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import junit.framework.*;

import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;
import net.sourceforge.czt.base.util.XmlWriterReaderTest;

/**
 * A JUnit test case for testing JaxbXmlReader and JaxbXmlWriter objects.
 *
 * @author Petra Malik
 */
public class JaxbXmlWriterReaderTest
  extends XmlWriterReaderTest
{
  public JaxbXmlWriterReaderTest()
  {
    super();
  }

  public JaxbXmlWriterReaderTest(String name)
  {
    super(name);
  }

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(JaxbXmlWriterReaderTest.class);
    return suite;
  }

  public XmlReader createXmlReader()
  {
    return new JaxbXmlReader();
  }

  public XmlWriter createXmlWriter()
  {
    return new JaxbXmlWriter();
  }

  public AstValidator createAstValidator()
  {
    return new JaxbValidator();
  }

  public List<URL> getExampleFiles()
  {
    List<URL> result = new ArrayList();
    result.add(getClass().getResource("/Sched.xml"));
    result.add(getClass().getResource("/birthdaybook.xml"));
    return result;
  }
}
