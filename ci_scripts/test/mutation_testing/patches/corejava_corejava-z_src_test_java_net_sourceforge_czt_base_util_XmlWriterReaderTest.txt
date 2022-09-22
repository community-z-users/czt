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

package net.sourceforge.czt.base.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.net.URL;
import java.util.List;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;

/**
 * <p>A JUnit test case for testing XmlReader and XmlWriter objects.</p>
 *
 * @author Petra Malik
 */
public abstract class XmlWriterReaderTest
  extends TestCase
{
  public XmlWriterReaderTest()
  {
    super();
  }

  public XmlWriterReaderTest(String name)
  {
    super(name);
  }

  /**
   * Returns the XmlReader to be tested.
   */
  public abstract XmlReader createXmlReader();

  /**
   * Returns the XmlWriter to be tested.
   */
  public abstract XmlWriter createXmlWriter();

  /**
   * Returns a list of file names that are used to perform the check.
   */
  public abstract List<URL> getExampleFiles();

  public final void testWritingReading()
    throws Exception
  {
    XmlReader reader = createXmlReader();
    XmlWriter writer = createXmlWriter();
    for (URL url : getExampleFiles()) {
      InputStream is = url.openStream();
      Term term;
      try {
        term = reader.read(is);
      } finally {
        is.close();
      }
      File tmpFile1 = File.createTempFile("cztXmlWriterReader", "test.zml");
      tmpFile1.deleteOnExit();
      writer.write(term, new FileOutputStream(tmpFile1));
      Term term2 = reader.read(tmpFile1);
      Assert.assertEquals(term, term2);

      File tmpFile2 = File.createTempFile("cztXmlWriterReader", "test.zml");
      tmpFile2.deleteOnExit();
      writer.setEncoding("UTF-16");
      writer.write(term, new FileOutputStream(tmpFile2));
      term2 = reader.read(tmpFile2);
      Assert.assertEquals(term, term2);
    }
  }
}
