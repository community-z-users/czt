/*
  Copyright 2003, 2006 Mark Utting
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

import java.util.List;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.visitor.TermVisitor;

import junit.framework.*;

/**
 * <p>A JUnit test case for testing Term objects.</p>
 *
 * @author Petra Malik
 */
public abstract class TermTest extends TestCase
{
  public TermTest(String name)
  {
    super(name);
  }

  /**
   * Returns the Term to be checked.
   */
  protected abstract Term createTerm();

  /**
   * Checks whether the term returned by #createTerm
   * accepts the array of children returned via Term.getChildren
   * as an argument given to Term.create.  The resulting term
   * must be equivalent to the original term.
   */
  public final void testCreateNewTerm()
  {
    Term term = createTerm();
    Term newTerm = term.create(term.getChildren());
    Assert.assertEquals(newTerm, term);
  }

  /**
   * Checks whether the term returned by #createTerm
   * accepts a Term visitor and calls the visitTerm method.
   */
  public final void testTermVisitor()
  {
    Term term = createTerm();
    Visitor<Object> visitor = new ExampleTermVisitor();
    Assert.assertEquals("ok", term.accept(visitor));
  }

  /**
   * An example visitor that visits Term objects.
   */
  private static class ExampleTermVisitor
    implements TermVisitor<Object>
  {
    public Object visitTerm(Term term)
    {
      return "ok";
    }
  }

  public final void testGetAnnsNotNull()
  {
    Term term = createTerm();
    Assert.assertNotNull("The Object to be checked is null", term);
    String message = term.getClass().toString() + ".getAnns() returns null";
    Assert.assertNotNull(message, term.getAnns());
  }

  public void testGetAnn()
  {
    Term term = createTerm();
    List<Object> anns = term.getAnns();
    anns.clear();
    String string = "Foo";
    anns.add(string);
    Assert.assertEquals(string, term.getAnn(Object.class));
    Assert.assertEquals(string, term.getAnn(String.class));
    Assert.assertNull(term.getAnn(java.util.List.class));
  }
}
