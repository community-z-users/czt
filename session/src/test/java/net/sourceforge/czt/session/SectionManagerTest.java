/*
  Copyright (C) 2005, 2006 Petra Malik
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

import junit.framework.*;

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

  public void testReset()
    throws CommandException
  {
    Key key1 = new Key("test1", String.class);
    Key key2 = new Key("prelude", String.class);
    Key key3 = new Key("test_toolkit", String.class);
    manager_.put(key1, "bar");
    manager_.put(key2, "foo");
    manager_.put(key3, "barfoot");
    assertNotNull(manager_.get(key1));
    assertNotNull(manager_.get(key2));
    assertNotNull(manager_.get(key3));
    manager_.reset();
    assertNotNull(manager_.get(key2));
    assertNotNull(manager_.get(key3));
    try {
      manager_.get(key1);
      fail("Should throw Exception");
    }
    catch (CommandException e) {
    }
  }
}
