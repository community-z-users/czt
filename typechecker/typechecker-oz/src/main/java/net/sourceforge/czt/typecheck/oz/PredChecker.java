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

import java.util.Iterator;
import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>PredChecker</code> instance visits the Pred instances in an
 * AST, checks the preds for type consistencies, adding an ErrorAnn if
 * there are inconsistencies.
 *
 * Each visit method returns a <code>UResult</code>, which indicates
 * that the types in the predicate have been partially unified, or
 * not.
 */
public class PredChecker
  extends Checker<UResult>
  implements ImpliesPredVisitor<UResult>,
             MemPredVisitor<UResult>,
             AndPredVisitor<UResult>,
             OrPredVisitor<UResult>,
             IffPredVisitor<UResult>,
             PredVisitor<UResult>
{
  //a Z pred checker
  protected net.sourceforge.czt.typecheck.z.PredChecker zPredChecker_;

  public PredChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPredChecker_ =
      new net.sourceforge.czt.typecheck.z.PredChecker(typeChecker);
  }

  public UResult visitTerm(Term term)
  {
    return term.accept(zPredChecker_);
  }

  public UResult visitImpliesPred(ImpliesPred impliesPred)
  {
    typeEnv().enterScope();
    UResult result = impliesPred.accept(zPredChecker_);
    typeEnv().exitScope();
    return result;
  }

  public UResult visitMemPred(MemPred memPred)
  {
    UResult result = memPred.accept(zPredChecker_);

    //if the left expr is a reference, and the right expr is a set of
    //object identifies, then try to downcast
    if (memPred.getLeftExpr() instanceof RefExpr &&
        memPred.getMixfix().equals(Boolean.FALSE)) {
      Type2 rightType = getType2FromAnns(memPred.getRightExpr());
      if (rightType instanceof PowerType &&
          powerType(rightType).getType() instanceof ClassType) {
        RefExpr refExpr = (RefExpr) memPred.getLeftExpr();
        Type2 leftType = getType2FromAnns(refExpr);
        PowerType rPowerType = (PowerType) rightType;
        ClassType classType = (ClassType) rPowerType.getType();

        //if weak unification is successful, then push the name into
        //the typing environment, and remove any type mismatch errors
        //added for the Z typechecker.
        UResult unified = weakUnify(leftType, classType);
        if (unified != FAIL && !(leftType instanceof UnknownType)) {
          //override, as long as the name is already in the environment
          ZName zName = factory().createZName(refExpr.getZName(), false);
          typeEnv().override(zName, classType);
          //remove any type mismatch errors
          String message =
            ErrorMessage.TYPE_MISMATCH_IN_MEM_PRED.toString();
          for (Iterator<Object> iter = memPred.getAnns().iterator(); iter.hasNext();) {
            Object next = iter.next();
            if (next instanceof ErrorAnn) {
              ErrorAnn errorAnn = (ErrorAnn) next;
              if (errorAnn.getErrorMessage().equals(message)) {
                iter.remove();
                removeObject(errorAnn, paraErrors());
              }
            }
          }
        }
      }
    }
    return result;
  }

  public UResult visitAndPred(AndPred andPred)
  {
    traverseForDowncasts(andPred);

    //AndPreds are visited separately because we do not enter a new
    //variable scope for them
    UResult result = andPred.accept(zPredChecker_);
    return result;
  }

  public UResult visitOrPred(OrPred orPred)
  {
    //enter a new variable scope to allow downcasts
    typeEnv().enterScope();

    //visit the left pred
    Pred leftPred = orPred.getLeftPred();
    UResult lSolved = leftPred.accept(predChecker());

    //enter a new variable scope to allow downcasts. The scope of the
    //left predicate is different to that of the right
    typeEnv().exitScope();
    typeEnv().enterScope();

    //visit the right pred
    Pred rightPred = orPred.getRightPred();
    UResult rSolved = rightPred.accept(predChecker());
    typeEnv().exitScope();

    //if either the left or right are partially solved, then
    //this predicate is also partially solved
    UResult result = UResult.conj(lSolved, rSolved);

    return result;
  }

  public UResult visitIffPred(IffPred iffPred)
  {
    typeEnv().enterScope();
    traverseForDowncasts(iffPred.getLeftPred());
    traverseForDowncasts(iffPred.getRightPred());
    UResult result = iffPred.accept(zPredChecker_);
    typeEnv().exitScope();
    return result;
  }

  public UResult visitPred(Pred pred)
  {
    //enter a new variable scope to allow downcasts
    typeEnv().enterScope();
    UResult result = pred.accept(zPredChecker_);
    typeEnv().exitScope();
    return result;
  }

  //remove an object from a list
  protected void removeObject(Object obj, List<Object> list)
  {
    for (Iterator<Object> iter = list.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (obj == next) {
        iter.remove();
      }
    }
  }
}
