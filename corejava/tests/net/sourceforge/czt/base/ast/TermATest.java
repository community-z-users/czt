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

package net.sourceforge.czt.base.ast;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.visitor.TermAVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;

import junit.framework.*;

/**
 * <p>A JUnit test case for testing TermA objects.</p>
 *
 * @author Petra Malik
 */
public abstract class TermATest
  extends TermTest
{
  public TermATest(String name)
  {
    super(name);
  }

  /**
   * Returns the TermA to be checked.
   */
  protected abstract TermA createTermA();
 
  protected final Term createTerm()
  {
    return createTermA();
  }

  public final void testGetAnnsNotNull()
  {
    TermA termA = createTermA();
    Assert.assertNotNull("The Object to be checked is null", termA);
    String message = termA.getClass().toString() + ".getAnns() returns null";
    Assert.assertNotNull(message, termA.getAnns());
  }

  /**
   * Checks whether the term returned by #createTerm
   * accepts a TermA visitor and calls the visitTermA method
   * (even when the visitTerm method is provided as well).
   */
  public final void testTermAVisitor()
  {
    Visitor visitor = new ExampleTermAVisitor();
    Assert.assertEquals("ok", createTermA().accept(visitor));
  }

  /**
   * An example visitor that visits Term and TermA objects.
   */
  private static class ExampleTermAVisitor
    implements TermAVisitor, TermVisitor
  {
    /**
     * Returns the String "not ok".
     */
    public Object visitTerm(Term term)
    {
      return "not ok";
    }

    /**
     * Returns the String "ok".
     */
    public Object visitTermA(TermA term)
    {
      return "ok";
    }
  }
}
