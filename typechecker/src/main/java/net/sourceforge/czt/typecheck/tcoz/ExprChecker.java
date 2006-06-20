/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.tcoz;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.tcoz.ast.*;
import net.sourceforge.czt.tcoz.visitor.*;
import net.sourceforge.czt.typecheck.oz.util.*;

/**
 * An <code>ExprChecker</code> instance visits the Exprs instances in
 * an AST, checks them for type consistencies, adding an ErrorAnn
 * if there are inconsistencies.
 *
 * Each visit method to Expr objects return the type (Type2) of the
 * expression.
 */
public class ExprChecker
  extends Checker<Type2>
  implements ChannelExprVisitor<Type2>
{
  //an Object-Z Expr checker
  protected net.sourceforge.czt.typecheck.oz.ExprChecker ozExprChecker_;

  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    ozExprChecker_ =
      new net.sourceforge.czt.typecheck.oz.ExprChecker(typeChecker);
  }

  public Type2 visitTerm(Term term)
  {
    return term.accept(ozExprChecker_);
  }

  public Type2 visitChannelExpr(ChannelExpr channelExpr)
  {
    ChannelType chanType = factory().createChannelType();
    Type2 result = factory().createPowerType(chanType);
    return result;
  }
}
