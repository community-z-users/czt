/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.session;

import java.io.*;

import junit.framework.*;

import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.z.ast.Spec;

public class SectionManagerTest
  extends TestCase
{
  protected SectionManager manager_;

  protected void setUp()
  {
    manager_ = new SectionManager();
  }

  protected void tearDown()
  {
    manager_ = null;
  }

  public void testParseSect()
  {
    try {
      File file = File.createTempFile("SectionManagerTest", ".tex");
      file.deleteOnExit();
      FileWriter writer = new FileWriter(file);
      String latexSpec =
	"\\begin{schema}{Test} a:\\nat \\where true \\end{schema}";
      writer.write(latexSpec, 0, latexSpec.length());
      writer.close();
      String filename = file.getCanonicalPath();
      Spec spec =
	(Spec) manager_.get(new Key(filename, Spec.class));
      assertTrue(spec != null);
    }
    catch (IOException e) {
      fail("Should not throw Exception " + e);
    }
  }

  public void testClone()
  {
    String s1 = "test1";
    String s2 = "yeah";
    String s3 = "test2";
    manager_.setProperty(s1, s2);
    SectionManager clone = (SectionManager) manager_.clone();
    assertEquals(clone.getProperty(s1), s2);
    assertTrue(manager_.getProperty(s3) == null);
    assertTrue(clone.getProperty(s3) == null);
    clone.setProperty(s3, s3);
    assertTrue(manager_.getProperty(s3) == null);
    assertEquals(clone.getProperty(s3), s3);
  }
}

