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

package net.sourceforge.czt.base.visitor;

import java.util.*;

import junit.framework.*;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A (JUnit) test for class VisitorUtils.
 */
public class VisitorUtilsTest extends TestCase
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  private Visitor visitor_ =  new TestVisitor();

  public static Test suite()
  {
    return new TestSuite(VisitorUtilsTest.class);
  }

  public void testVisitList()
  {
    List list = new Vector();
    VisitorUtils.visitList(visitor_, list);
    list.add(factory_.createInStroke());
    list.add("Blubb");
    list.add(factory_.createParent());
    VisitorUtils.visitList(visitor_, list);
    assertEquals(((Parent) list.get(2)).getWord(), "Visited");
    list.add(null);
    VisitorUtils.visitList(visitor_, list);
  }

  /**
   * A test visitor.
   */
  class TestVisitor
    implements ParentVisitor
  {
    public Object visitParent(Parent parent)
    {
      parent.setWord("Visited");
      return null;
    }
  }
}

