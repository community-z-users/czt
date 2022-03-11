/*
  Copyright (C) 2004, 2007 Petra Malik
  This file is part of the CZT project: http://czt.sourceforge.net

  The CZT project contains free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as published
  by the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License along
  with CZT; if not, write to the Free Software Foundation, Inc.,
  59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.util;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

/**
 * A (JUnit) test class for testing the LatexMarkupFunction class.
 *
 * @author Petra Malik
 */
public class LatexMarkupFunctionTest
  extends TestCase
{
  private final ZFactory factory_ = new ZFactoryImpl();

  private static final String fooCommand_ = "\foo";
  private static final String fooUnicode_ = "foo";
  private final DirectiveType fooType_ = DirectiveType.NONE;
  private final Directive directiveFoo_ =
      factory_.createDirective(fooCommand_, fooUnicode_, fooType_);

  private static final String barCommand_ = "\bar";
  private static final String barUnicode_ = "bar";
  private final DirectiveType barType_ = DirectiveType.IN;
  private final Directive directiveBar_ =
    factory_.createDirective(barCommand_, barUnicode_, barType_);

  private static final String section_ = "Specification";
  private LatexMarkupFunction markupFunction_;
  
  private final Dialect dialect_ = Dialect.Z;

  @Override
public void setUp()
  {
    markupFunction_ = new LatexMarkupFunction(section_);
  }

  public void testSimpleAddAndRetrieve()
  {
    try {
      markupFunction_.add(dialect_, directiveBar_);
    }
    catch (MarkupException e) {
      fail("Should not throw MarkupException!");
    }
    MarkupDirective markupDirective =
      markupFunction_.getCommandDirective(barCommand_);
    Assert.assertEquals(markupDirective.getCommand(), barCommand_);
    Assert.assertEquals(markupDirective.getUnicode(), barUnicode_);
    Assert.assertEquals(markupDirective.getType(), barType_);
    Assert.assertEquals(markupDirective.getSection(), section_);
  }

  public void testAddDirectiveTwice()
  {
    try {
      markupFunction_.add(dialect_, directiveFoo_);
      markupFunction_.add(dialect_, directiveBar_);
    }
    catch (MarkupException e) {
      fail("Should not throw MarkupException!");
    }
    try {
      markupFunction_.add(dialect_, directiveBar_);
      fail("Should throw MarkupException!");
    }
    catch (MarkupException ok) {
      // ok
    }
    try {
      Directive d =
        factory_.createDirective(barCommand_, barUnicode_, barType_);
      markupFunction_.add(dialect_, d);
      fail("Should throw MarkupException!");
    }
    catch (MarkupException ok) {
      // ok
    }
  }

  public void testInheritDirectiveFromParent()
  {
    try {
      LatexMarkupFunction parent =
        new LatexMarkupFunction("parent");
      parent.add(dialect_, directiveBar_);
      markupFunction_.add(parent);
      MarkupDirective directive =
        markupFunction_.getCommandDirective(barCommand_);
      Assert.assertTrue(directive != null);
    }
    catch (MarkupException e) {
      fail("Should not throw MarkupException!");
    }
  }

  public void testInheritSameDirectiveFromDifferentParents()
  {
    try {
      LatexMarkupFunction markupFunction1 =
        new LatexMarkupFunction("parent");
      markupFunction1.add(dialect_, directiveBar_);
      markupFunction_.add(markupFunction1);
      MarkupDirective directive =
        markupFunction_.getCommandDirective(barCommand_);
      Assert.assertTrue(directive != null);
      LatexMarkupFunction markupFunction2 =
        new LatexMarkupFunction("parent");
      markupFunction2.add(dialect_, directiveFoo_);
      markupFunction_.add(markupFunction2);
      directive =
        markupFunction_.getCommandDirective(barCommand_);
      Assert.assertTrue(directive != null);
    }
    catch (MarkupException e) {
      fail("Should not throw MarkupException!");
    }
  }
}
