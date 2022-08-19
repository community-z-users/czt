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

import junit.framework.TestCase;

public class SectionManagerTest
  extends TestCase  implements Command
{
  protected SectionManager manager_;

  @Override
  protected void setUp()
  {
    manager_ = new SectionManager(Dialect.Z);
    manager_.putCommand(String.class, this);
  }

  @Override
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
    SectionManager clone = manager_.clone();
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
    Key<String> key1 = new Key<String>("test1", String.class);
    Key<String> key2 = new Key<String>("prelude", String.class);
    Key<String> key3 = new Key<String>("test_toolkit", String.class);
    manager_.put(key1, "bar");
    manager_.put(key2, "foo");
    manager_.put(key3, "barfoot");
    String value = manager_.get(key1);
    assertNotNull(value);
    assertNotNull(manager_.get(key2));
    assertNotNull(manager_.get(key3));
    manager_.reset();
    value = manager_.get(key2);
    assertNotNull(value);
    assertNotNull(manager_.get(key3));
    //manager_.get(key1);
    if (manager_.isCached(key1) || !manager_.isCached(key2))
      fail("Should throw Exception");
  }
  
  public void testCachedAndRetrieveKey()
  {
    Key<String> key1 = new Key<String>("test1", String.class);
    Key<String> key2 = new Key<String>("prelude", String.class);
    Key<String> key3 = new Key<String>("test_toolkit", String.class);
    String value1 = "bar";
    String value2 = "foo";
    String value3 = "barfoot";
    manager_.put(key1, value1);
    manager_.put(key2, value2);    
    assertTrue(manager_.isCached(key1));
    assertTrue(manager_.isCached(key2));    
    assertFalse(manager_.isCached(key3));
    Key<?> key1_ = manager_.retrieveKey(value1);
    Key<?> key2_ = manager_.retrieveKey(value2);    
    Key<?> key3_ = manager_.retrieveKey(value3);
    assertNotNull(key1_);
    assertNotNull(key2_);
    assertNull(key3_);
    assertEquals(key1, key1_);
    assertEquals(key2, key2_);        
  }

  @Override
  public boolean compute(String name, SectionManager manager) throws CommandException
  {
    manager.endTransaction(new Key<String>(name, String.class), name);
    return true;
  }
}
