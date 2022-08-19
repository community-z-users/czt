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

import junit.framework.*;

/**
 * A (junit) test class for testing delegator.
 */
public class DelegatorTest extends TestCase
{
  private Object delegator_;

  public static Test suite()
  {
    return new TestSuite(DelegatorTest.class);
  }

  protected void setUp()
  {
    Class<?>[] interfaces = {Foo.class, Bar.class };
    Object[] impls = {new FooImpl(), new BarImpl() };

    delegator_ = Delegator.newInstance(interfaces, impls);
  }

  public void testInstanceOf()
  {
    Assert.assertTrue(delegator_ instanceof Foo);
    Assert.assertTrue(delegator_ instanceof Bar);
  }

  public void testInvoke1()
  {
    Foo foo = (Foo) delegator_;
    Assert.assertTrue(foo.foo());
  }

  public void testInvoke2()
  {
    Bar bar = (Bar) delegator_;
    Assert.assertTrue(bar.bar());
  }

  /**
   * An interface with one method.
   */
  interface Foo
  {
    boolean foo();
  }

  /**
   * An interface with one method.
   */
  interface Bar
  {
    boolean bar();
  }

  /**
   * An implementation of interface Foo.
   */
  static class FooImpl implements Foo
  {
    public boolean foo()
    {
      return true;
    }
  }

  /**
   * An implementation of interface Foo.
   */
  static class BarImpl implements Bar
  {
    public boolean bar()
    {
      return true;
    }
  }
}
