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

package net.sourceforge.czt.print.zeves;

/**
 *
 * @author Leo Freitas
 * @date Jul 19, 2011
 */
public class ZToWhyMPrintVisitor {}
//        implements TermVisitor<String>,
//                   SpecVisitor<String>,
//                   ZSectVisitor<String>,
//                   ParentVisitor<String>
//{
//
//  protected String visit(Term t)
//  {
//    if (t == null)
//    {
//      return "";
//    }
//    else
//    {
//      return t.accept(this);
//    }
//  }
//
//
//  @Override
//  public String visitTerm(Term zedObject)
//  {
//    throw new UnsupportedOperationException("Cannot transform " + zedObject + " to WhyM.vdmsl");
//  }
//
//  @Override
//  public String visitSpec(Spec term)
//  {
//    StringBuilder result = new StringBuilder();
//    for(Sect s : term.getSect())
//    {
//      result.append(visit(s));
//    }
//    return result.toString();
//  }
//
//  @Override
//  public String visitZSect(ZSect term)
//  {
//    term.getName();
//    term.getParent();
//    for(Para p : term.getZParaList())
//    {
//      visit(p);
//    }
//  }
//
//  @Override
//  public String visitParent(Parent term)
//  {
//    sectTypeEnvAnn = sectInfo().get(new Key<SectTypeEnvAnn>(parentName, SectTypeEnvAnn.class));
//  }
//
//
//
//}
