/*
Copyright (C) 2004 Petra Malik
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

import junit.framework.*;

import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

public class LatexMarkupFunctionTest
  extends TestCase
{
  private final ZFactory factory_ = new ZFactoryImpl();

  private final String fooCommand_ = "\foo";
  private final String fooUnicode_ = "foo";
  private final DirectiveType fooType_ = DirectiveType.NONE;
  private Directive directiveFoo_ =
      factory_.createDirective(fooCommand_, fooUnicode_, fooType_);

  private final String barCommand_ = "\bar";
  private final String barUnicode_ = "bar";
  private final DirectiveType barType_ = DirectiveType.IN;
  private Directive directiveBar_ =
    factory_.createDirective(barCommand_, barUnicode_, barType_);

  private final String section_ = "Specification";
  private LatexMarkupFunction markupFunction_;

  public void setUp()
  {
    markupFunction_ = new LatexMarkupFunction(section_);
  }

  public void testSimpleAddAndRetrieve()
  {
    try {
      markupFunction_.add(directiveBar_);
    }
    catch(MarkupException e) {
      fail("Should not throw MarkupException!");
    }
    LatexMarkupFunction.MarkupDirective markupDirective =
      markupFunction_.getCommandDirective(barCommand_);
    Assert.assertEquals(markupDirective.getCommand(), barCommand_);
    Assert.assertEquals(markupDirective.getUnicode(), barUnicode_);
    Assert.assertEquals(markupDirective.getType(), barType_);
    Assert.assertEquals(markupDirective.getSection(), section_);
  }

  public void testAddDirectiveTwice()
  {
    try {
      markupFunction_.add(directiveFoo_);
      markupFunction_.add(directiveBar_);
    }
    catch(MarkupException e) {
      fail("Should not throw MarkupException!");
    }
    try {
      markupFunction_.add(directiveBar_);
      fail("Should throw MarkupException!");
    }
    catch(MarkupException ok) {
      // ok
    }
    try {
      Directive d =
        factory_.createDirective(barCommand_, barUnicode_, barType_);
      markupFunction_.add(d);
      fail("Should throw MarkupException!");
    }
    catch(MarkupException ok) {
      // ok
    }
  }

  public void testInheritDirectiveFromParent()
  {
    try {
      LatexMarkupFunction parent =
        new LatexMarkupFunction("parent");
      parent.add(directiveBar_);
      markupFunction_.add(parent);
      LatexMarkupFunction.MarkupDirective directive =
        markupFunction_.getCommandDirective(barCommand_);
      Assert.assertTrue(directive != null);
    }
    catch(MarkupException e) {
      fail("Should not throw MarkupException!");
    }
  }

  public void testInheritSameDirectiveFromDifferentParents()
  {
    try {
      LatexMarkupFunction markupFunction1 =
        new LatexMarkupFunction("parent");
      markupFunction1.add(directiveBar_);
      markupFunction_.add(markupFunction1);
      LatexMarkupFunction.MarkupDirective directive =
        markupFunction_.getCommandDirective(barCommand_);
      Assert.assertTrue(directive != null);
      LatexMarkupFunction markupFunction2 =
        new LatexMarkupFunction("parent");
      markupFunction2.add(directiveFoo_);
      markupFunction_.add(markupFunction2);
      directive =
        markupFunction_.getCommandDirective(barCommand_);
      Assert.assertTrue(directive != null);
    }
    catch(MarkupException e) {
      fail("Should not throw MarkupException!");
    }
  }
}
