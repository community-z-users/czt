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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.RenameList;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;

/**
 *
 * @author Leo Freitas
 * @date Aug 4, 2011
 */
public final class ZEvesUtils
{

  private ZEvesUtils()
  {
  }

  public static ZEvesLabel getLabel(Term term)
  {
    ZEvesLabel result = null;
    //if (term instanceof Pred || term instanceof ConjPara)
    //{
      result = term.getAnn(ZEvesLabel.class);
    //}
    return result;
  }

  public static InstantiationList assertInstantiationList(Term term)
  {
    if (term instanceof InstantiationList) {
      return (InstantiationList) term;
    }
    final String message =
      "Expected a InstantiationList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static InstantiationList assertRenameListAsInstantiationList(RenameExpr term)
  {
    RenameList result = term.getRenameList();
    if (result instanceof InstantiationList) {
      return (InstantiationList)result;
    }
    final String message = "Expected the Z/Eves instantiation list implementation of RenameList " +
      " but found " + String.valueOf(result);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public static InstantiationList getInstantiationListFromExpr(Expr term)
  {
    InstantiationList result = null;
    if (term instanceof RenameExpr)
    {
      return assertRenameListAsInstantiationList((RenameExpr)term);
    }
    return result;
  }
}
