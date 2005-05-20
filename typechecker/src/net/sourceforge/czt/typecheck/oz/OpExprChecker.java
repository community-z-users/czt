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
package net.sourceforge.czt.typecheck.oz;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.oz.impl.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.z.*;

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
    AnonOpExprVisitor,
    OpPromotionExprVisitor,
    OpExpr2Visitor,
    SeqOpExprVisitor,
    ParallelOpExprVisitor,
    AssoParallelOpExprVisitor,
    HideOpExprVisitor,
    RenameOpExprVisitor,
    ScopeEnrichOpExprVisitor,
    OpTextVisitor,
    OpExprVisitor
{
  public OpExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Object visitOpExpr(OpExpr opExpr)
  {
    return factory().createSignature();
  }


  public Object visitAnonOpExpr(AnonOpExpr anonOpExpr)
  {
    //get the signature of the operation text
    OpText opText = anonOpExpr.getOpText();
    Signature signature = (Signature) opText.accept(opExprChecker());

    //add the signature annotation
    addSignatureAnn(anonOpExpr, signature);

    return signature;
  }

  public Object visitOpText(OpText opText)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get the class signature for "self"
    ClassType selfType = getSelfType();
    ClassSig selfSig = selfType.getClassSig();

    //check that each name in the delta list is a primary variable
    List<RefName> deltaList = opText.getDelta();
    for (RefName delta : deltaList) {
      DeclName declName = factory().createDeclName(delta);
      if (!primary().contains(declName)) {
        Object [] params = {delta};
        error(delta, ErrorMessage.NON_PRIMDECL_IN_DELTALIST, params);
      }
    }

    //visit the schema text and gets its signature
    SchText schText = opText.getSchText();
    Signature signature = (Signature) schText.accept(exprChecker());

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(opText, signature);

    return signature;
  }

  public Object visitOpPromotionExpr(OpPromotionExpr opPromExpr)
  {
    Signature signature = factory().createVariableSignature();

    Expr expr = opPromExpr.getExpr();
    Type2 exprType = getSelfType();

    //if the expression is not null, then we use the type of expr
    if (expr != null) {
      exprType = (Type2) expr.accept(exprChecker());
    }
    //get the type of the expression
    //Type2 exprType = (Type2) expr.accept(exprChecker());

    VariableClassType vClassType = factory().createVariableClassType();
    vClassType.complete();
    UResult unified = unify(vClassType, exprType);
    //if the type is not a class type, raise an error
    if (unified == FAIL) {
      Object [] params = {opPromExpr, exprType};
      error(opPromExpr, ErrorMessage.NON_CLASS_IN_OPPROMEXPR, params);
    }
    else {
      ClassSig cSig = vClassType.getClassSig();
      if (!instanceOf(cSig, VariableClassSig.class)) {
        RefName refName = opPromExpr.getName();
        NameSignaturePair opDef = findOperation(refName, cSig);
        if (opDef == null) {
          Object [] params = {opPromExpr};
          error(opPromExpr, ErrorMessage.NON_EXISTENT_NAME_IN_OPPROMEXPR, params);
        }
        else {
          signature = opDef.getSignature();
        }
      }
    }

    //add the signature annotation
    addSignatureAnn(opPromExpr, signature);

    return signature;
  }

  /**
   * Visits ConjOpExprs and ExChoiceOpExpr which have the same type
   * rules.
   */
  public Object visitOpExpr2(OpExpr2 opExpr2)
  {
    Signature signature = factory().createVariableSignature();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = opExpr2.getLeftOpExpr();
    OpExpr rOpExpr = opExpr2.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    if (!instanceOf(lSig, VariableSignature.class) &&
        !instanceOf(rSig, VariableSignature.class)) {
      List<NameTypePair> newPairs = list(lSig.getNameTypePair());
      newPairs.addAll(rSig.getNameTypePair());
      checkForDuplicates(newPairs, opExpr2,
                         ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);
      signature = factory().createSignature(newPairs);
    }

    //add the signature annotation
    addSignatureAnn(opExpr2, signature);

    return signature;
  }

  public Object visitSeqOpExpr(SeqOpExpr seqOpExpr)
  {
    Signature signature = factory().createVariableSignature();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = seqOpExpr.getLeftOpExpr();
    OpExpr rOpExpr = seqOpExpr.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    if (!instanceOf(lSig, VariableSignature.class) &&
        !instanceOf(rSig, VariableSignature.class)) {
      String errorMessage = ErrorMessage.TYPE_MISMATCH_IN_SEQOPEXPR.toString();
      signature = createCompSig(lSig, rSig, seqOpExpr, errorMessage);
      checkForDuplicates(signature.getNameTypePair(), seqOpExpr,
                         ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);
    }

    //add the signature annotation
    addSignatureAnn(seqOpExpr, signature);

    return signature;
  }

  public Object visitParallelOpExpr(ParallelOpExpr parallelOpExpr)
  {
    Signature signature = factory().createVariableSignature();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = parallelOpExpr.getLeftOpExpr();
    OpExpr rOpExpr = parallelOpExpr.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    if (!instanceOf(lSig, VariableSignature.class) &&
        !instanceOf(rSig, VariableSignature.class)) {
      String errorMessage =
        ErrorMessage.TYPE_MISMATCH_IN_PARALLELOPEXPR.toString();
      Signature sigA = createPipeSig(lSig, rSig, parallelOpExpr, errorMessage);
      Signature sigB = createPipeSig(rSig, lSig, parallelOpExpr, errorMessage);
      signature = intersect(sigA, sigB);
      checkForDuplicates(signature.getNameTypePair(), parallelOpExpr,
                         ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);
    }

    //add the signature annotation
    addSignatureAnn(parallelOpExpr, signature);

    return signature;
  }

  public Object visitAssoParallelOpExpr(AssoParallelOpExpr assoParallelOpExpr)
  {
    Signature signature = factory().createVariableSignature();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = assoParallelOpExpr.getLeftOpExpr();
    OpExpr rOpExpr = assoParallelOpExpr.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    if (!instanceOf(lSig, VariableSignature.class) &&
        !instanceOf(rSig, VariableSignature.class)) {
      String errorMessage =
        ErrorMessage.TYPE_MISMATCH_IN_ASSOPARALLELOPEXPR.toString();
      Signature sigA = createPloSig(lSig, rSig, assoParallelOpExpr, errorMessage);
      Signature sigB = createPloSig(rSig, lSig, assoParallelOpExpr, errorMessage);
      signature = intersect(sigA, sigB);
      checkForDuplicates(signature.getNameTypePair(), assoParallelOpExpr,
                         ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);
    }

    //add the signature annotation
    addSignatureAnn(assoParallelOpExpr, signature);

    return signature;
  }

  public Object visitHideOpExpr(HideOpExpr hideOpExpr)
  {
    Signature signature = factory().createVariableSignature();

    //get the signature of the operation expr
    OpExpr opExpr = hideOpExpr.getOpExpr();
    Signature hideSig = (Signature) opExpr.accept(opExprChecker());

    //hide the declarations
    if (!instanceOf(hideSig, VariableSignature.class)) {
      signature = createHideSig(hideSig, hideOpExpr.getName(), hideOpExpr);
    }
    return signature;
  }

  public Object visitRenameOpExpr(RenameOpExpr renameOpExpr)
  {
    Signature signature = factory().createVariableSignature();

    //get the signature of the operation expr
    OpExpr opExpr = renameOpExpr.getOpExpr();
    Signature renameSig = (Signature) opExpr.accept(opExprChecker());

    //hide the declarations
    if (!instanceOf(renameSig, VariableSignature.class)) {
        String errorMessage =
          ErrorMessage.DUPLICATE_NAME_IN_RENAMEOPEXPR.toString();
        List<NameNamePair> namePairs = renameOpExpr.getNameNamePair();
        signature = createRenameSig(renameSig, namePairs,
                                    renameOpExpr, errorMessage);
        checkForDuplicates(signature.getNameTypePair(), renameOpExpr);
    }
    return signature;
  }

  public Object visitScopeEnrichOpExpr(ScopeEnrichOpExpr scopeEnrichOpExpr)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get the signature of the left operation expression
    OpExpr lOpExpr = scopeEnrichOpExpr.getLeftOpExpr();
    Signature signature = (Signature) lOpExpr.accept(opExprChecker());

    //add the types into the typing environment
    typeEnv().add(signature.getNameTypePair());

    //get and visit the right expr
    OpExpr rOpExpr = scopeEnrichOpExpr.getRightOpExpr();
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    //check that the signatures of the two expressions are disjoint
    List<NameTypePair> pairsA = signature.getNameTypePair();
    List<NameTypePair> pairsB = rSig.getNameTypePair();
    for (NameTypePair pairA : pairsA) {
      NameTypePair pairB = findInSignature(pairA.getName(), rSig);
      if (pairB != null) {
	Object [] params = {pairA.getName(), scopeEnrichOpExpr};
	error(scopeEnrichOpExpr,
	      ErrorMessage.DUPLICATE_NAME_IN_SCOPEENRICHOPEXPR, params);
      }
    }

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(scopeEnrichOpExpr, signature);

    return signature;
  }
}
