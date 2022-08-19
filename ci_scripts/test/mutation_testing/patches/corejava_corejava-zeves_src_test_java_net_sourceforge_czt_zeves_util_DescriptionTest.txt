/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.zeves.util;

import junit.framework.TestCase;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.zeves.ast.ProofCommand;

/**
 *
 * @author Leo Freitas
 * @date Aug 9, 2011
 */
public class DescriptionTest extends TestCase {

  private final static String SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.z.util.ShortDescriptionResourceBundle";
  private final static String ZEVES_SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.zeves.util.ShortDescriptionResourceBundle";

//  public void testShortDescription()
//  {
//    ShortDescriptionResourceBundle s = new ShortDescriptionResourceBundle();
//    System.out.println(s.getContents());
//  }
//
//  public void testLongDescription()
//  {
//    LongDescriptionResourceBundle s = new LongDescriptionResourceBundle();
//    System.out.println(s.getContents());
//  }

  public void testSymbolVisitorShort()
  {
    Visitor<String> zevesShortDescriptionVisitor_ = new ZEvesConcreteSyntaxDescriptionVisitor(SHORT_DESCRIPTION_RESOURCE, ZEVES_SHORT_DESCRIPTION_RESOURCE);
    System.out.println(zevesShortDescriptionVisitor_.toString());

    ProofCommand cmd = ZEvesUtils.FACTORY.getZEvesFactory().createGlobalInvokeCommand();
    String st = cmd.accept(zevesShortDescriptionVisitor_);
    System.out.println(st);
  }

  public void testSymbolVisitorLong()
  {
    Visitor<String> zevesLongDescriptionVisitor_ = new ZEvesConcreteSyntaxDescriptionVisitor();
    System.out.println(zevesLongDescriptionVisitor_.toString());

    ProofCommand cmd = ZEvesUtils.FACTORY.getZEvesFactory().createGlobalInvokeCommand();
    String st = cmd.accept(zevesLongDescriptionVisitor_);
    System.out.println(st);

    Expr expr = ZEvesUtils.FACTORY.createNumExpr(10);
    st = expr.accept(zevesLongDescriptionVisitor_);
    System.out.println(st);
  }

}
