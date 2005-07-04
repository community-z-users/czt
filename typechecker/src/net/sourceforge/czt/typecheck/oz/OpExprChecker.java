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
package net.sourceforge.czt.typecheck.oz;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

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
    DistOpExprVisitor,
    OpTextVisitor
{
  public OpExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
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
    ClassSig selfSig = getSelfSig();

    //check that each name in the delta list is a primary variable
    DeltaList deltaList = opText.getDeltaList();
    if (deltaList != null) {
      List<RefName> refNames = deltaList.getRefName();
      for (RefName delta : refNames) {
        DeclName declName = factory().createDeclName(delta);
        if (!primary().contains(declName)) {
          Object [] params = {delta};
          error(delta, ErrorMessage.NON_PRIMDECL_IN_DELTALIST, params);
        }
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
      exprType = resolveClassType(exprType);
    }

    //if the type is not a class type, raise an error
    if (!instanceOf(exprType, ClassType.class) &&
        !instanceOf(exprType, VariableType.class)) {
      Object [] params = {opPromExpr, exprType};
      error(opPromExpr, ErrorMessage.NON_CLASS_IN_OPPROMEXPR, params);
    }
    else if (!instanceOf(exprType, VariableType.class)) {
      ClassType classType = (ClassType) exprType;
      ClassSig cSig = classType.getClassSig();
      if (!instanceOf(cSig, VariableClassSig.class)) {
        RefName refName = opPromExpr.getName();
        NameSignaturePair opDef = findOperation(refName, cSig);

        //if the name is not found, and use-before-decl is enabled,
        //then search for this name in the class
        if (opDef == null && sectTypeEnv().getSecondTime() &&
            (expr == null || isSelfExpr(expr))) {
          List<Operation> ops = classPara().getOperation();
          for (Operation op : ops) {
            if (namesEqual(op.getName(), refName)) {
              opDef = (NameSignaturePair) op.accept(paraChecker());
            }
          }
        }

        //if there is no operation with this name, raise an error
        if (opDef == null) {
          Object [] params = {opPromExpr};
          error(opPromExpr, ErrorMessage.NON_EXISTENT_NAME_IN_OPPROMEXPR, params);
        }
        else {
          signature = opDef.getSignature();
          if (resolve(signature) instanceof VariableSignature) {
            Object [] params = {opPromExpr};
            error(opPromExpr, ErrorMessage.SIGNATURE_NOT_DETERMINED, params);
          }
        }

        //if there is an operation, but it is not visible, raise an error
        if (opDef != null && !isVisible(refName, classType)) {
          Object [] params = {refName, opPromExpr};
          error(opPromExpr, ErrorMessage.NON_VISIBLE_NAME_IN_OPPROMEXPR, params);
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
    //enter a new scope
    typeEnv().enterScope();

    if (opExpr2 instanceof ConjOpExpr) {
      traverseForDowncasts(opExpr2);
    }

    //get the signatures of the left and right operations
    OpExpr lOpExpr = opExpr2.getLeftOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());

    //if this is a choice expr, exit and then enter a scope so that
    //downcasts in the left and not visible in the right
    if (opExpr2 instanceof ExChoiceOpExpr) {
      typeEnv().exitScope();
      typeEnv().enterScope();
    }

    OpExpr rOpExpr = opExpr2.getRightOpExpr();
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    List<NameTypePair> newPairs = list(lSig.getNameTypePair());
    newPairs.addAll(rSig.getNameTypePair());
    checkForDuplicates(newPairs, opExpr2,
                       ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);
    Signature signature = factory().createSignature(newPairs);

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(opExpr2, signature);

    return signature;
  }

  public Object visitSeqOpExpr(SeqOpExpr seqOpExpr)
  {
    //enter a new scope
    typeEnv().enterScope();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = seqOpExpr.getLeftOpExpr();
    OpExpr rOpExpr = seqOpExpr.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    String errorMessage = ErrorMessage.TYPE_MISMATCH_IN_SEQOPEXPR.toString();
    Signature signature = createCompSig(lSig, rSig, seqOpExpr, errorMessage);
    checkForDuplicates(signature.getNameTypePair(), seqOpExpr,
                       ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(seqOpExpr, signature);

    return signature;
  }

  public Object visitParallelOpExpr(ParallelOpExpr parallelOpExpr)
  {
    //enter a variable scope
    typeEnv().enterScope();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = parallelOpExpr.getLeftOpExpr();
    OpExpr rOpExpr = parallelOpExpr.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    String errorMessage =
      ErrorMessage.TYPE_MISMATCH_IN_PARALLELOPEXPR.toString();
    Signature sigA = createPipeSig(lSig, rSig, parallelOpExpr, errorMessage);
    Signature sigB = createPipeSig(rSig, lSig, parallelOpExpr, errorMessage);
    Signature signature = intersect(sigA, sigB);
    checkForDuplicates(signature.getNameTypePair(), parallelOpExpr,
                       ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(parallelOpExpr, signature);

    return signature;
  }

  public Object visitAssoParallelOpExpr(AssoParallelOpExpr assoParallelOpExpr)
  {
    //enter a variable scope
    typeEnv().enterScope();

    //get the signatures of the left and right operations
    OpExpr lOpExpr = assoParallelOpExpr.getLeftOpExpr();
    OpExpr rOpExpr = assoParallelOpExpr.getRightOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    String errorMessage =
      ErrorMessage.TYPE_MISMATCH_IN_ASSOPARALLELOPEXPR.toString();
    Signature sigA =
      createPloSig(lSig, rSig, assoParallelOpExpr, errorMessage);
    Signature sigB =
      createPloSig(rSig, lSig, assoParallelOpExpr, errorMessage);
    Signature signature = intersect(sigA, sigB);
    checkForDuplicates(signature.getNameTypePair(), assoParallelOpExpr,
                       ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(assoParallelOpExpr, signature);

    return signature;
  }

  public Object visitHideOpExpr(HideOpExpr hideOpExpr)
  {
    //get the signature of the operation expr
    OpExpr opExpr = hideOpExpr.getOpExpr();
    Signature hideSig = (Signature) opExpr.accept(opExprChecker());

    //hide the declarations
    Signature signature =
      createHideSig(hideSig, hideOpExpr.getName(), hideOpExpr);

    //add the signature annotation
    addSignatureAnn(hideOpExpr, signature);

    return signature;
  }

  public Object visitRenameOpExpr(RenameOpExpr renameOpExpr)
  {
    //get the signature of the operation expr
    OpExpr opExpr = renameOpExpr.getOpExpr();
    Signature renameSig = (Signature) opExpr.accept(opExprChecker());

    //hide the declarations
    String errorMessage =
      ErrorMessage.DUPLICATE_NAME_IN_RENAMEOPEXPR.toString();
    List<NameNamePair> namePairs = renameOpExpr.getNameNamePair();
    Signature signature = createRenameSig(renameSig, namePairs,
                                          renameOpExpr, errorMessage);
    checkForDuplicates(signature.getNameTypePair(), renameOpExpr);

    //add the signature annotation
    addSignatureAnn(renameOpExpr, signature);

    return signature;
  }

  public Object visitScopeEnrichOpExpr(ScopeEnrichOpExpr scopeEnrichOpExpr)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get the signature of the left operation expression
    OpExpr lOpExpr = scopeEnrichOpExpr.getLeftOpExpr();
    Signature lSig = (Signature) lOpExpr.accept(opExprChecker());

    //add the types into the typing environment
    typeEnv().add(lSig.getNameTypePair());

    //get and visit the right expr
    OpExpr rOpExpr = scopeEnrichOpExpr.getRightOpExpr();
    Signature rSig = (Signature) rOpExpr.accept(opExprChecker());

    List<NameTypePair> newPairs = list(lSig.getNameTypePair());
    newPairs.addAll(rSig.getNameTypePair());
    checkForDuplicates(newPairs, scopeEnrichOpExpr,
                       ErrorMessage.TYPE_MISMATCH_IN_OPEXPR2);

    //exit the variable scope
    typeEnv().exitScope();

    //creat the signature of this operation
    Signature signature = factory().createSignature(newPairs);

    //add the signature annotation
    addSignatureAnn(scopeEnrichOpExpr, signature);

    return signature;
  }

  public Object visitDistOpExpr(DistOpExpr distOpExpr)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get the signature from the schema text. The ExprChecker will add
    //the declarations to the typing environment
    SchText schText = distOpExpr.getSchText();
    Signature distSig = (Signature) schText.accept(exprChecker());

    //get the signature of the operation expression
    //this is the signature of the entire distributed operation
    OpExpr opExpr = distOpExpr.getOpExpr();
    Signature signature = (Signature) opExpr.accept(opExprChecker());

    //check that there are no common names between the distributed
    //operator declarations and the op expr declarations
    List<NameTypePair> distPairs = distSig.getNameTypePair();
    for (NameTypePair distPair : distPairs) {
      DeclName distName = distPair.getName();
      NameTypePair opExprPair = findNameTypePair(distName, signature);
      if (opExprPair != null) {
        Object [] params = {distName, distOpExpr};
        error(distOpExpr, ErrorMessage.DUPLICATE_NAME_IN_DISTOPEXPR, params);
      }
    }

    //distributed sequential operations have an additional type
    //rule. Implementing it here rather than using its own visit
    //simplifies things somewhat
    if (distOpExpr instanceof DistSeqOpExpr) {
      for (NameTypePair distPair : distPairs) {
        DeclName distName = distPair.getName();
        List<Stroke> strokes = list(distName.getStroke());
        int size = strokes.size();
        if (size > 0 && strokes.get(size - 1) instanceof OutStroke) {
          strokes.remove(size - 1);
          DeclName baseName = factory().createDeclName(distName.getWord(),
                                                       strokes, null);
          NameTypePair opExprPair = findNameTypePair(baseName, signature);
          if (opExprPair != null) {
            Object [] params = {distName, baseName, distOpExpr};
            error(distOpExpr, ErrorMessage.DUPLICATE_OUTNAME_IN_DISTOPEXPR, params);
          }
        }
      }
    }

    //exit the variable scope
    typeEnv().exitScope();

    //add the signature annotation
    addSignatureAnn(distOpExpr, signature);

    return signature;
  }
}
