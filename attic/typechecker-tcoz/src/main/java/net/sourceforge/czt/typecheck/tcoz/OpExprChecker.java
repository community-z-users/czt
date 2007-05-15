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
import static net.sourceforge.czt.z.util.ZUtils.*;

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
  extends Checker<Signature>
  implements
    AtProExprVisitor<Signature>,
    RecProExprVisitor<Signature>,
    WaitUntilProExprVisitor<Signature>,
    EventVisitor<Signature>
{
  //an Object-Z OpExpr checker
  protected net.sourceforge.czt.typecheck.oz.OpExprChecker ozOpExprChecker_;

  public OpExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    ozOpExprChecker_ =
      new net.sourceforge.czt.typecheck.oz.OpExprChecker(typeChecker);
  }

  public Signature visitTerm(Term term)
  {
    return term.accept(ozOpExprChecker_);
  }

  public Signature visitAtProExpr(AtProExpr atProExpr)
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

  public Signature visitRecProExpr(RecProExpr recProExpr)
  {
    Signature signature = factory().createSignature();

    ZName opRefName = assertZName(recProExpr.getOpName());
    ZName opName = factory().createZName(opRefName, false);
    ClassType selfType = getSelfType();
    List<NameSignaturePair> opPairs = selfType.getOperation();
    NameSignaturePair existing = findNameSigPair(opName, opPairs);
    if (existing != null) {
      System.err.println("Name " + opName + " already an operation");
    }
    else {
      NameSignaturePair temporaryPair =
	factory().createNameSignaturePair(opName, factory().createSignature());
      opPairs.add(temporaryPair);
      OpExpr opExpr = recProExpr.getOpExpr();
      signature = (Signature) opExpr.accept(opExprChecker());
      removeObject(opPairs, temporaryPair);
    }
    return signature;
  }

  public Signature visitWaitUntilProExpr(WaitUntilProExpr waitUntilProExpr)
  {
    OpExpr opExpr = waitUntilProExpr.getOpExpr();
    Signature signature = (Signature) opExpr.accept(opExprChecker());

    Expr expr = waitUntilProExpr.getWaitUntil();
    Type2 exprType = (Type2) expr.accept(exprChecker());


    return signature;
  }

  public Signature visitEvent(Event event)
  {
    ZName channelName = assertZName(event.getChannelName());
    LocAnn locAnn = (LocAnn) channelName.getAnn(LocAnn.class);
    ZName baseChannelName = factory().createZName(channelName.getWord());
    addAnn(baseChannelName, locAnn);
    RefExpr channelRef = factory().createRefExpr(baseChannelName);
    Type2 channelRefType = (Type2) channelRef.accept(exprChecker());

    Type2 chanType = factory().createChannelType();
    UResult result = unify(channelRefType, chanType);
    if (result == FAIL) {
      System.err.println("Name " + channelRef.getName() + " not a channel");
    }
    
    Expr expr = event.getExpr();
    if (expr != null) {
      expr.accept(exprChecker());
    }

    return null;
  }
}
