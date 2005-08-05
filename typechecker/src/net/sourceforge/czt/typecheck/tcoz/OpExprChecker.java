/*
  Copyright (C) 2004, 2005 Tim Miller
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY  WARRANTY; without even the implied warranty of
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
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.tcoz.ast.*;
import net.sourceforge.czt.tcoz.visitor.*;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.tcoz.util.*;

/**
 * An <code>OpChecker</code> instance visits the OpExprs instances in
 * an AST, checks them for type consistencies, adding an ErrorAnn
 * if there are inconsistencies.
 *
 * Each visit method to OpExpr objects return the signature of the
 * expression.
 */
public class OpExprChecker
  extends Checker
  implements
    AtProExprVisitor,
    EventVisitor
{
  //an Object-Z OpExpr checker
  protected net.sourceforge.czt.typecheck.oz.OpExprChecker ozOpExprChecker_;

  public OpExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    ozOpExprChecker_ =
      new net.sourceforge.czt.typecheck.oz.OpExprChecker(typeChecker);
  }

  public Object visitTerm(Term term)
  {
    return term.accept(ozOpExprChecker_);
  }

  public Object visitAtProExpr(AtProExpr atProExpr)
  {
    Event event = atProExpr.getEvent();
    event.accept(opExprChecker());

    //visit the OpExor, using its signature as the signature of this AtProExpr
    OpExpr opExpr = atProExpr.getOpExpr();
    Signature signature = (Signature) opExpr.accept(opExprChecker());

    //add the signature annotation
    addSignatureAnn(atProExpr, signature);

    return signature;
  }

  public Object visitEvent(Event event)
  {
    RefName name = event.getName();
    Type nameType = getType(name);

    if (nameType instanceof GenericType) {
      System.err.println("channel is generic");
    }
    else {
      Type2 chanType = factory().createChannelType();
      UResult result = unify((Type2) nameType, chanType);
      if (result == FAIL) {
	System.err.println("Name " + name + " not a channel");
      }
    }

    Expr expr = event.getExpr();
    if (expr != null) {
      expr.accept(exprChecker());
    }

    return null;
  }
}
