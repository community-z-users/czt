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

package net.sourceforge.czt.util;

import java.util.*;

import junit.framework.*;

/**
 * A (junit) test class for testing typesafe lists.
 */
public class TypesafeListTest extends TestCase
{
  /**
   * A typesafe list of Boolean.
   */
  private List booleanList_;

  public static Test suite()
  {
    return new TestSuite(TypesafeListTest.class);
  }

  protected void setUp()
  {
    booleanList_ = new TypesafeList(Boolean.class);
  }

  public void testAddingAndGettingRightType()
  {
    final Boolean myTrue = Boolean.valueOf(true);
    final Boolean myFalse = Boolean.valueOf(false);
    booleanList_.add(myTrue);
    booleanList_.add(myFalse);
    Assert.assertEquals(booleanList_.size(), 2);
    Assert.assertSame(myTrue, booleanList_.get(0));
    Assert.assertSame(myFalse, booleanList_.get(1));
  }

  public void testAddingWrongType()
  {
    try {
      booleanList_.add("String");
      fail("Should throw a ClassCastException");
    }
    catch (IllegalArgumentException ok) { }
    try {
      booleanList_.add(0, "String");
      fail("Should throw a NullPointerException");
    }
    catch (IllegalArgumentException ok) { }
    Collection collection = new ArrayList();
    collection.add("String");
    try {
      booleanList_.addAll(collection);
      fail("Should throw a NullPointerException");
    }
    catch (IllegalArgumentException ok) { }
  }

  public void testAddingNull()
  {
    try {
      booleanList_.add(null);
      fail("Should throw a NullPointerException");
    }
    catch (IllegalArgumentException ok) { }
    try {
      booleanList_.add(0, null);
      fail("Should throw a NullPointerException");
    }
    catch (IllegalArgumentException ok) { }
    Collection collection = new ArrayList();
    collection.add(null);
    try {
      booleanList_.addAll(collection);
      fail("Should throw a NullPointerException");
    }
    catch (IllegalArgumentException ok) { }
  }

  public void testContainingOrGettingNull()
  {
    try {
      Assert.assertFalse(booleanList_.contains(null));
    }
    catch (NullPointerException ok) { }
    try {
      Assert.assertEquals(-1, booleanList_.indexOf(null));
    }
    catch (NullPointerException ok) { }
  }

  public void testAddInheritedClass()
  {
    String string = "Hello";
    List serializableList = new TypesafeList(java.io.Serializable.class);
    serializableList.add(string);
    Assert.assertSame(string, serializableList.get(0));
  }

  public void testEquals()
  {
    final Boolean myTrue = Boolean.valueOf(true);
    final Boolean myFalse = Boolean.valueOf(false);

    List list = new ArrayList();
    list.add(myTrue);
    list.add(myFalse);
    list.add(myFalse);
    booleanList_.addAll(list);
    Assert.assertTrue(booleanList_.equals(list));
    Assert.assertTrue(list.equals(booleanList_));
  }

  public void testListMethods()
  {
    final Boolean myTrue = Boolean.valueOf(true);
    final Boolean myFalse = Boolean.valueOf(false);

    Collection collection = new ArrayList();
    collection.add(myTrue);
    int nElements = 0;

    booleanList_.add(myTrue); nElements++;
    booleanList_.add(0, myFalse); nElements++;
    Assert.assertSame(myFalse, booleanList_.get(0));
    booleanList_.addAll(collection); nElements++;
    Assert.assertEquals(nElements, booleanList_.size());
    booleanList_.addAll(0, collection); nElements++;
    Assert.assertEquals(nElements, booleanList_.size());
    Assert.assertSame(myTrue, booleanList_.get(0));
    Assert.assertTrue(booleanList_.contains(myTrue));
    Assert.assertTrue(booleanList_.contains(myFalse));
    Assert.assertTrue(booleanList_.containsAll(collection));
    Assert.assertFalse(booleanList_.isEmpty());
  }
}
