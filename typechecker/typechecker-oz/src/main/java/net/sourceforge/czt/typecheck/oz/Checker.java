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

//import static net.sourceforge.czt.z.util.ZUtils.*;
import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.oz.util.*;
import net.sourceforge.czt.typecheck.oz.impl.*;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract public class Checker<R>
  extends net.sourceforge.czt.typecheck.z.Checker<R>
{
  //the information required for the typechecker classes.
  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    typeChecker_ = typeChecker;
  }

  //a Factory for creating Object-Z terms
  protected Factory factory()
  {
    return typeChecker_.getFactory();
  }

  //the operation expr checker
  protected Checker<Signature> opExprChecker()
  {
    return typeChecker_.opExprChecker_;
  }

  //typing environment used in downcasting
  protected TypeEnv downcastEnv()
  {
    return typeChecker_.downcastEnv_;
  }

  //the current class name
  protected ZName className()
  {
    ZName result = null;
    if (typeChecker_.classPara_ != null) {
      result = typeChecker_.classPara_.getClassName();
    }
    return result;
  }

  //the current class para
  protected ClassPara classPara()
  {
    return typeChecker_.classPara_;
  }

  //set the current class paragraph
  protected void setClassPara(ClassPara classPara)
  {
    typeChecker_.classPara_ = classPara;
    factory().addNameID(classPara.getClassName());
  }

  //the lst of primary state variables in the current class
  protected List<ZName> primary()
  {
    return typeChecker_.primary_;
  }

  //reset the list of primary variables in the current class to empty
  protected void resetPrimary()
  {
    typeChecker_.primary_.clear();
  }

  protected void error(Term term, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error, params);
    error(term, errorAnn);
  }

  protected void error(Term term,
                       net.sourceforge.czt.typecheck.z.ErrorMessage error,
                       Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error.toString(), params);
    error(term, errorAnn);
  }

  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
                                     sectName(), nearestLocAnn(term),
                                     markup());
    return errorAnn;
  }

  protected ErrorAnn errorAnn(Term term, String error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
                                     sectName(), nearestLocAnn(term),
                                     markup());
    return errorAnn;
  }

  protected UResult weakUnify(Type2 typeA, Type2 typeB)
  {
    UnificationEnv unificationEnv = (UnificationEnv) unificationEnv();
    return unificationEnv.weakUnify(typeA, typeB);
  }

  //adds the class name to a given type, so that the class name can be
  //including in error messages.
  public void addContext(GivenType givenType)
  {
    if (classPara() != null) {
      ClassDeclAnn classDeclAnn =  new ClassDeclAnn(className());
      addAnn(givenType, classDeclAnn);
    }
  }

  protected Type getType(ZName zName)
  {
    //first look up the name in the downcast environment
    Type type = downcastEnv().getType(zName);
    if (type instanceof UnknownType) {
      type = super.getType(zName);
    }
    else {
      //if this is ok, remove the undeclared annotation
      removeAnn(zName, UndeclaredAnn.class);
    }
    return type;
  }

  //go through a series of conjunctions to see if there is a downcast
  //so that downcasts can be performed either before or after the
  //predicate in which they are used.
  protected void traverseForDowncasts(Pred pred)
  {
    if (pred instanceof AndPred) {
      Pred2 pred2 = (Pred2) pred;
      Pred leftPred = pred2.getLeftPred();
      Pred rightPred = pred2.getRightPred();
      traverseForDowncasts(leftPred);
      traverseForDowncasts(rightPred);
    }
    else if  (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      boolean mixfix = memPred.getMixfix().booleanValue();
      if (!mixfix) {
        memPred.accept(predChecker());
      }
    }
  }

  //go through a series of conj op exprs to see if there is a downcast
  //so that downcasts can be performed either before or after the
  //predicate in which they are used.
  protected void traverseForDowncasts(OpExpr opExpr)
  {
    if (opExpr instanceof ConjOpExpr) {
      ConjOpExpr conjOpExpr = (ConjOpExpr) opExpr;
      for (OpExpr oe : conjOpExpr.getOpExpr()) {
        traverseForDowncasts(oe);
      }
    }
    else if (opExpr instanceof ScopeEnrichOpExpr) {
      ScopeEnrichOpExpr scopeEnrichOpExpr = (ScopeEnrichOpExpr) opExpr;
      OpExpr leftOpExpr = scopeEnrichOpExpr.getOpExpr().get(0);
      traverseForDowncasts(leftOpExpr);
    }
    else if (opExpr instanceof AnonOpExpr) {
      AnonOpExpr anonOpExpr = (AnonOpExpr) opExpr;
      OpText opText = anonOpExpr.getOpText();
      ZSchText zSchText = opText.getZSchText();

      //the list of Names declared in this schema text
      List<NameTypePair> pairs = factory().list();

      //get and visit the list of declarations
      DeclList declList = zSchText.getDeclList();
      ZUtils.insert(pairs, declList.accept(declChecker()));
      //pairs.addAll(declList.accept(declChecker()));

      //we use a different downcasting environment because we do not
      //want to add the declarations into the typing environment, but
      //we need to downcasts in the environment
      downcastEnv().enterScope();
      for (NameTypePair pair : pairs) {
        downcastEnv().add(pair.getZName(), pair.getType());
      }
      if (zSchText.getPred() != null) {
        traverseForDowncasts(zSchText.getPred());
      }
      downcastEnv().exitScope();
    }
  }

  protected ZName getZName(Expr expr)
  {
    ZName result = null;
    if (expr instanceof RenameExpr) {
      RenameExpr renameExpr = (RenameExpr) expr;
      result = getZName(renameExpr.getExpr());
    }
    else if (expr instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) expr;
      ZName zRefName = refExpr.getZName();
      result = factory().createZName(zRefName, false);
    }
    else {
      assert false;
    }
    return result;
  }

  protected List<ClassRef> getSuperClasses(ClassRefType classRefType)
  {
    List<ClassRef> visited = factory().list(classRefType.getThisClass());
    return getSuperClasses(classRefType, visited);
  }

  protected List<ClassRef> getSuperClasses(ClassRefType classRefType,
                                           List<ClassRef> visited)
  {
    List<ClassRef> superClasses = factory().list(classRefType.getSuperClass());
    List<ClassRef> superSuperClasses = factory().list();
    for (ClassRef superClass : superClasses) {
      Type2 type = unwrapType(getType(superClass.getName()));
      if (type instanceof PowerType &&
          powerType(type).getType() instanceof ClassRefType) {
        ClassRefType superClassType =
          (ClassRefType) powerType(type).getType();

        //add the super class itself
        if (!contains(superSuperClasses, superClassType.getThisClass())) {
          superSuperClasses.add(superClassType.getThisClass());
        }

        //for each superclass, get its superclasses, and add
        List<ClassRef> superClassRefs = superClassType.getSuperClass();
        for (ClassRef next : superClassRefs) {
          //do not search if this has already been looked up
          if (!contains(visited, next)) {
            visited.add(next);
            List<ClassRef> nextSuperClasses =
              getSuperClasses(superClassType, visited);
            //add all transitive superclass if not already present
            for (ClassRef nextSuperClass : nextSuperClasses) {
              if (!contains(superSuperClasses, nextSuperClass)) {
                superSuperClasses.add(nextSuperClass);
              }
            }
          }
        }
      }
      else {
        assert false : "Type of " + superClass.getName() + " : " + type;
      }
    }

    //add the transitive superclasses to the superclass list
    for (ClassRef superSuperClass : superSuperClasses) {
      if (!contains(superClasses, superSuperClass)) {
        superClasses.add(superSuperClass);
      }
    }
    return superClasses;
  }

  protected void inheritFeature(List<NameTypePair> source,
                                List<NameTypePair> target,
                                Expr expr)
  {
    for (NameTypePair pair : source) {
      ZName sourceName = pair.getZName();
      if (!isSelfName(sourceName)) {
        NameTypePair existing = findNameTypePair(sourceName, target);
        if (existing != null) {
          Type2 sourceType = unwrapType(pair.getType());
          Type2 existingType = unwrapType(existing.getType());
          UResult unified = unify(sourceType, existingType);
          if (unified == FAIL) {
            Object [] params = {sourceName, expr, sourceType, existingType};
            error(expr, ErrorMessage.INCOMPATIBLE_INHERIT, params);
          }
        }
        else {
          typeEnv().add(pair);
          //target.add(pair);
          ZUtils.insert(target, pair);
        }
      }
    }
  }

  protected void inheritOps(List<NameSignaturePair> source,
                            List<NameSignaturePair> target,
                            Expr expr)
  {
    for (NameSignaturePair pair : source) {
      ZName sourceName = pair.getZName();
      NameSignaturePair existing = findNameSigPair(sourceName, target);
      if (existing != null) {
        Signature sourceSignature = pair.getSignature();
        Signature existingSignature = existing.getSignature();
        List<NameTypePair> conjoinedPairs =
          factory().list(sourceSignature.getNameTypePair());
        ZUtils.insert(conjoinedPairs, existingSignature.getNameTypePair());
        //conjoinedPairs.addAll(existingSignature.getNameTypePair());
        List<Term> params = factory().list();
        params.add(expr);
        params.add(sourceName);
        checkForDuplicates(conjoinedPairs, params,
                           ErrorMessage.INCOMPATIBLE_OP_INHERIT.toString());
      }
      else {
        target.add(pair);
      }
    }
  }

  //get the type of "self"
  protected ClassRefType getSelfType()
  {
    ZName zName = factory().createZName(OzString.SELF);
    RefExpr refExpr = factory().createRefExpr(zName);
    Type2 selfType = (Type2) refExpr.accept(exprChecker());
    assert selfType instanceof ClassRefType;
    ClassRefType result = (ClassRefType) selfType;
    return result;
  }


  //returns true if and only if the expressions is a reference to the
  //variable "self"
  protected boolean isSelfExpr(Expr expr)
  {
    boolean result = false;
    if (expr instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) expr;
      ZName zName = refExpr.getZName();
      result = zName.getWord().equals(OzString.SELF) &&
        zName.getZStrokeList().size() == 0;
    }
    return result;
  }

  //take the intersection of 2 signatures
  protected Signature intersect(Signature sigA, Signature sigB)
  {
    Signature signature = factory().createSignature();
    List<NameTypePair> pairsA = sigA.getNameTypePair();
    //List<NameTypePair> pairsB = 
    			sigB.getNameTypePair();
    for (NameTypePair pairA : pairsA) {
      NameTypePair pairB = findNameTypePair(pairA.getZName(), sigB);
      if (pairB != null) {
        ZUtils.insert(signature.getNameTypePair(), pairA);
        ZUtils.insert(signature.getNameTypePair(), pairB);
        //signature.getNameTypePair().add(pairA);
        //signature.getNameTypePair().add(pairB);
      }
    }
    return signature;
  }

  //merge two class types.
  protected void merge(ClassType newType, ClassType oldType, Term term)
  {
    //merge the attributes
    List<NameTypePair> attrDecls = newType.getAttribute();
    ZUtils.insert(attrDecls, oldType.getAttribute());
    //attrDecls.addAll(oldType.getAttribute());
    checkForDuplicates(attrDecls, term, ErrorMessage.INCOMPATIBLE_OVERRIDING);

    //merge the state signature
    List<NameTypePair> stateDecls = newType.getState().getNameTypePair();
    //stateDecls.addAll(oldType.getState().getNameTypePair());
    ZUtils.insert(stateDecls, oldType.getState().getNameTypePair());
    checkForDuplicates(stateDecls, term, ErrorMessage.INCOMPATIBLE_OVERRIDING);

    //merge the operations
    List<NameSignaturePair> newPairs = newType.getOperation();
    for (NameSignaturePair newPair : newPairs) {
      ZName zName = newPair.getZName();
      NameSignaturePair oldPair = findNameSigPair(zName, oldType.getOperation());
      if (oldPair == null) {
        newType.getOperation().add(newPair);
      }
      else {
        UResult unified = unify(oldPair.getSignature(), newPair.getSignature());
        if (unified == FAIL) {
          Object [] params = {zName, term};
          error(zName, ErrorMessage.INCOMPATIBLE_OVERRIDING, params);
        }
      }
    }
  }

  public void addImplicitOps()
  {
    //do nothing for Object-Z
  }

  protected void addOperation(ZName opName, Signature signature, ClassType classType)
  {
//    List<NameSignaturePair> ops = 
	  		classType.getOperation();
    NameSignaturePair existing = findOperation(opName, classType);

    //if there is already a pair, check it is compatible with the new definition
    if (existing != null) {
      List<NameTypePair> pairs = factory().list(signature.getNameTypePair());
      ZUtils.insert(pairs, existing.getSignature().getNameTypePair());
      //pairs.addAll(existing.getSignature().getNameTypePair());
      checkForDuplicates(pairs, opName, ErrorMessage.INCOMPATIBLE_OP_OVERRIDING);
      Signature newSig = factory().createSignature(pairs);
      NameSignaturePair newPair = factory().createNameSignaturePair(opName, newSig);
      classType.getOperation().remove(existing);
      classType.getOperation().add(newPair);
    }
    else {
      NameSignaturePair op = factory().createNameSignaturePair(opName, signature);
      classType.getOperation().add(op);
    }
  }

  protected void checkForDuplicates(List<NameTypePair> pairs,
                                    Term term,
                                    ErrorMessage error)
  {
    checkForDuplicates(pairs, term, error.toString());
  }

  //check for duplicate names a class paragraph
  protected void checkForDuplicates(List<ZName> zNames)
  {
    for (int i = 0; i < zNames.size(); i++) {
      ZName first = zNames.get(i);
      for (int j = i + 1; j < zNames.size(); j++) {
        ZName second = zNames.get(j);
        if (ZUtils.namesEqual(first, second)) {
          Object [] params = {second, className()};
          error(second, ErrorMessage.REDECLARED_NAME_IN_CLASSPARA, params);
        }
      }
    }
  }

  //check for duplicates in a class paragraph, and that names in the
  //visibility list are names of features in the class
  protected void checkClass(ClassType classType,
                            Term term,
                            VisibilityList visibilityList,
                            ErrorMessage errorMessage)
  {
    List<ZName> declNames = factory().list();
    if (className() != null) {
      declNames.add(className());
    }

    //collect the names
    List<NameTypePair> attrDecls = classType.getAttribute();
    for (NameTypePair pair : attrDecls) {
      declNames.add(pair.getZName());
    }
    Signature stateSig = classType.getState();
    List<NameTypePair> stateDecls = stateSig.getNameTypePair();
    for (NameTypePair pair : stateDecls) {
      declNames.add(pair.getZName());
    }
    List<NameSignaturePair> opDecls = classType.getOperation();
    for (NameSignaturePair pair : opDecls) {
      declNames.add(pair.getZName());
    }

    //check for duplicate names
    for (int i = 0; i < declNames.size(); i++) {
      ZName first = declNames.get(i);
      for (int j = i + 1; j < declNames.size(); j++) {
        ZName second = declNames.get(j);
        if (ZUtils.namesEqual(first, second) &&
            !ZUtils.idsEqual(first.getId(), second.getId())) {
          Object [] params = {first, term};
          error(first, errorMessage, params);
        }
      }
    }

    //check that all names in the visibility list are features of this class
    if (visibilityList != null) {
      for (ZName visibleName : visibilityList) {
        boolean found = false;
        for (ZName featureName : declNames) {
          if (ZUtils.namesEqual(featureName, visibleName) &&
              !ZUtils.namesEqual(className(), visibleName)) {
            found = true;
            break;
          }
        }
        if (!found) {
          Object [] params = {visibleName, className()};
          error(visibleName,
                ErrorMessage.NON_EXISTENT_NAME_IN_VISIBILITYLIST,
                params);
        }
      }
    }
  }

  //check that each visible feature of a class is visible in a subclass
  protected void checkVisibility(ClassRefType superClass,
                                 ClassRefType subClass,
                                 List<NameTypePair> superPairs,
                                 List<NameTypePair> subPairs,
                                 PolyExpr polyExpr)
  {
    for (NameTypePair superPair : superPairs) {
      ZName superName = factory().createZName(superPair.getZName(), false);
      if (isVisible(superName, superClass)) {
        //if this feature is visible in the super class, it must be visible
        //in the subclass as well
        NameTypePair subPair = findNameTypePair(superName, subPairs);
        if (subPair == null || !isVisible(superName, subClass)) {
          Object [] params = {subClass.getThisClass().getName(),
                              superName,
                              superClass.getThisClass().getName(),
                              polyExpr};
          error(polyExpr,
                ErrorMessage.NON_VISIBLE_FEATURE_IN_POLYEXPR, params);
        }
      }
    }
  }

  protected void checkOpVisibility(ClassRefType superClass,
                                   ClassRefType subClass,
                                   List<NameSignaturePair> superPairs,
                                   List<NameSignaturePair> subPairs,
                                   PolyExpr polyExpr)
  {
    for (NameSignaturePair superPair : superPairs) {
      ZName superName = factory().createZName(superPair.getZName(), false);
      if (isVisible(superName, superClass)) {
        NameSignaturePair subPair = findNameSigPair(superName, subPairs);
        //if this operation is visible in the super class, it must be
        //visible in the subclass as well
        if (subPair == null || !isVisible(superName, subClass)) {
          Object [] params = {subClass.getThisClass().getName(),
                              superName,
                              superClass.getThisClass().getName(),
                              polyExpr};

          error(polyExpr,
                ErrorMessage.NON_VISIBLE_FEATURE_IN_POLYEXPR, params);
        }
        //if it is visible, the signatures must be compatible
        else if (subPair != null) {
          Signature superSig = superPair.getSignature();
          Signature subSig = subPair.getSignature();
          UResult unified = unify(superSig, subSig);
          if (unified == FAIL) {
            Object [] params = {superName, polyExpr,
                                subClass.getThisClass().getName(),
                                superClass.getThisClass().getName(),
                                superSig, subSig};

            error(polyExpr,
                  ErrorMessage.INCOMPATIBLE_OP_IN_POLYEXPR, params);
          }
        }

      }
    }
  }

  protected Signature createPloSig(Signature lSig, Signature rSig,
                                   Term term, String errorMessage)
  {
    //b3 and b4 correspond to the variable names "\Beta_3" and
    //"\Beta_4" in the standard for piping expr
    List<NameTypePair> b3Pairs = factory().list(lSig.getNameTypePair());
    List<NameTypePair> b4Pairs = factory().list(rSig.getNameTypePair());
    List<NameTypePair> rPairs = rSig.getNameTypePair();

    for (NameTypePair rPair : rPairs) {
      ZName rName = rPair.getZName();
      ZStrokeList strokes = factory().getZFactory().createZStrokeList();
      strokes.addAll(rName.getZStrokeList());
      int size = strokes.size();
      if (size > 0 && strokes.get(size - 1) instanceof InStroke) {
        OutStroke out = factory().createOutStroke();
        strokes.set(size - 1, out);
        ZName sName = factory().createZDeclName(rName.getWord(), strokes);
        NameTypePair foundPair = findNameTypePair(sName, lSig);
        if (foundPair != null) {
          Type2 fType = unwrapType(foundPair.getType());
          Type2 rType = unwrapType(rPair.getType());
          UResult unified = unify(fType, rType);
          if (unified == FAIL) {
            Object [] params = {term, sName, fType, rName, rType};
            error(term, errorMessage, params);
          }
          b4Pairs.remove(rPair);
        }
      }
    }
    //create the signature
    //    b3Pairs.addAll(b4Pairs);
    ZUtils.insert(b3Pairs, b4Pairs);
    Signature result = factory().createSignature(b3Pairs);
    return result;
  }

  //rename the operations is a list
  protected List<NameSignaturePair> renameOps(List<NameSignaturePair> ops,
                                              List<NewOldPair> renamePairs)
  {
    List<NameSignaturePair> newPairs = factory().list();
    for (NameSignaturePair pair : ops) {
      NewOldPair renamePair = findNewOldPair(pair.getZName(), renamePairs);
      if (renamePair != null) {
        ZName newName = renamePair.getZDeclName();
        NameSignaturePair newPair =
          factory().createNameSignaturePair(newName, pair.getSignature());
        newPairs.add(newPair);
      }
      else {
        newPairs.add(pair);
      }
    }
    return newPairs;
  }

  //rename the references in a class ref
  protected ClassRefList renameClassRefs(ClassRefList classRefs,
					 List<NewOldPair> renamePairs)
  {
    ClassRefList newClassRefs = factory().createClassRefList();
    for (ClassRef classRef : classRefs) {
      ClassRef newClassRef = renameClassRef(classRef, renamePairs);
      newClassRefs.add(newClassRef);
    }
    return newClassRefs;
  }

  //rename the primary names in a class
  protected List<Name> renamePrimary(List<Name> primaryNames,
                                         List<NewOldPair> renamePairs)
  {
    List<Name> newPrimaryNames = factory().list();
    for (Name primaryName : primaryNames) {
      ZName zPrimaryName = ZUtils.assertZName(primaryName);
      NewOldPair renamePair = findNewOldPair(zPrimaryName, renamePairs);
      if (renamePair == null) {
        newPrimaryNames.add(zPrimaryName);
      }
      else {
        newPrimaryNames.add(renamePair.getZDeclName());
      }
    }
    return newPrimaryNames;
  }

  //rename the features in a class
  protected ClassRefType createRenameClassType(ClassRefType classType,
                                               RenameExpr renameExpr,
                                               String errorMessage)
  {
    List<NewOldPair> renamePairs = renameExpr.getZRenameList();
    checkForDuplicateRenames(renamePairs, renameExpr,  errorMessage);

    ClassRefList classRefs = classType.getClasses();
    ClassRefList newClassRefs = renameClassRefs(classRefs, renamePairs);

    List<NameTypePair> attrs = classType.getAttribute();
    Signature attrSig = factory().createSignature(attrs);
    Signature newAttrSig = rename(attrSig, renamePairs);
    List<NameTypePair> newAttrs = newAttrSig.getNameTypePair();

    Signature state = classType.getState();
    Signature newState = rename(state, renamePairs);

    List<NameSignaturePair> ops = classType.getOperation();
    List<NameSignaturePair> newOps = renameOps(ops, renamePairs);

    ClassRef newThisClass =
      renameClassRef(classType.getThisClass(), renameExpr.getZRenameList());
    List<Name> newPrimary =
      renamePrimary(classType.getPrimary(), renameExpr.getZRenameList());
    ClassRefType result =
      factory().createClassRefType(newClassRefs, newState, newAttrs, newOps,
                                   newThisClass, classType.getSuperClass(),
                                   classType.getVisibilityList(), newPrimary);
    checkClass(result, renameExpr, null, ErrorMessage.REDECLARED_NAME_IN_RENAMEEXPR);
    return result;
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();
    //if this is a class type, instantiate it
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      if (!(classType instanceof VariableClassType)) {
        //instantiate the state
        Signature state = classType.getState();
        Signature newState = null;
        if (state != null) {
          newState = instantiate(state);
        }

        //instantiate the attributes
        List<NameTypePair> attrs = classType.getAttribute();
        List<NameTypePair> newAttrs = instantiatePairs(attrs);

        //instantiate the operations
        List<NameSignaturePair> ops = classType.getOperation();
        List<NameSignaturePair> newOps = factory().list();
        for (NameSignaturePair pair : ops) {
          Signature signature = instantiate(pair.getSignature());
          NameSignaturePair newPair =
            factory().createNameSignaturePair(pair.getZName(), signature);
          newOps.add(newPair);
        }

        //instaniate the class references
        ClassRefList classRefs = classType.getClasses();
        ClassRefList newClassRefs = factory().createClassRefList();
        for (ClassRef classRef : classRefs) {
          List<Type2> types = instantiateTypes(classRef.getType());
          List<NewOldPair> pairs = factory().list();
          ClassRef newClassRef =
            factory().createClassRef(classRef.getName(), types, pairs);
          newClassRefs.add(newClassRef);
        }

        if (type instanceof ClassRefType) {
          ClassRefType classRefType = (ClassRefType) type;
          ClassRef newThisClass = instantiate(classRefType.getThisClass());
          result = factory().createClassRefType(newClassRefs, newState, newAttrs,
                                                newOps, newThisClass,
                                                classRefType.getSuperClass(),
                                                classRefType.getVisibilityList(),
                                                classRefType.getPrimary());
        }
        else if (type instanceof ClassPolyType) {
          ClassPolyType classPolyType = (ClassPolyType) type;
          ClassRef newRootClass = instantiate(classPolyType.getRootClass());
          result = factory().createClassPolyType(newClassRefs, newState, newAttrs,
                                                 newOps, newRootClass);
        }
        else if (type instanceof ClassUnionType) {
          //ClassUnionType classUnionType = (ClassUnionType) type;
          result = factory().createClassUnionType(newClassRefs, newState, 
                                                  newAttrs, newOps);
        }
      }
      else if (type instanceof VariableClassType) {
        VariableClassType vcType = (VariableClassType) type;
        VariableClassType resultVC = factory().createVariableClassType();
        if (vcType.getCandidateType() != null) {
          Type2 instCandidateType = (Type2) instantiate(vcType.getCandidateType());
          assert instCandidateType instanceof ClassType;
          resultVC.setCandidateType((ClassType) instCandidateType);
        }
        result = resultVC;
      }
    }
    //if not a class type, use the Z typechecker's instantiate method
    else {
      result = super.instantiate(type);
    }
    return result;
  }

  protected ClassRef instantiate(ClassRef classRef)
  {
    List<Type2> types = instantiateTypes(classRef.getType());
    List<NewOldPair> pairs = factory().list(classRef.getNewOldPair());
    ClassRef result =
      factory().createClassRef(classRef.getName(), types, pairs);
    return result;
  }

  protected List<ClassRef> getClasses(Type2 type)
  {
    List<ClassRef> classes = factory().list();
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      classes = classType.getClasses();
    }
    return classes;
  }

  //find an attribute in a class signature
  protected NameTypePair findAttribute(ZName zName, ClassType classType)
  {
    NameTypePair result = findNameTypePair(zName, classType.getAttribute());
    return result;
  }

  //find a state variable in a class signature
  protected NameTypePair findStateDecl(ZName zName, ClassType classType)
  {
    List<NameTypePair> decls = classType.getState().getNameTypePair();
    NameTypePair result = findNameTypePair(zName, decls);
    return result;
  }

  //find a NameSignaturePair in a class signature
  protected NameSignaturePair findOperation(ZName zName, ClassType classType)
  {
    //problem with static import from GlobalDefs
    return GlobalDefs.findOperation(zName, classType);
  }

  protected NameSignaturePair findNameSigPair(ZName zName,
                                              List<NameSignaturePair> pairs)
  {
    //problem with static import from GlobalDefs
    return GlobalDefs.findNameSigPair(zName, pairs);
  }

  protected ClassRef findRef(ZName zName, List<ClassRef> classRefs)
  {
    ClassRef result = null;
    for (ClassRef classRef : classRefs) {
      if (ZUtils.namesEqual(zName, classRef.getName())) {
        result = classRef;
      }
    }
    return result;
  }

  protected Type2 resolveUnknownType(Type2 type)
  {
    Type2 result = super.resolveUnknownType(type);
    if (type instanceof UnknownType) {
      UnknownType uType = (UnknownType) type;
      result = renameClassType(result, uType.getPairs());
    }
    return result;
  }

  protected Type2 renameClassType(Type2 type, List<NewOldPair> pairs)
  {
    Type2 result = type;
    if (type instanceof ClassRefType && pairs.size() > 0) {
      ClassRefType classRefType = (ClassRefType) type;

      ClassRefList classRefs = classRefType.getClasses();
      ClassRefList newClassRefs = renameClassRefs(classRefs, pairs);

      List<NameTypePair> attrs = classRefType.getAttribute();
      Signature attrSig = factory().createSignature(attrs);
      Signature newAttrSig = rename(attrSig, pairs);
      List<NameTypePair> newAttrs = newAttrSig.getNameTypePair();

      Signature state = classRefType.getState();
      Signature newState = rename(state, pairs);

      List<NameSignaturePair> ops = classRefType.getOperation();
      List<NameSignaturePair> newOps = renameOps(ops, pairs);

      result = factory().createClassRefType(newClassRefs, newState, newAttrs, newOps,
                                            classRefType.getThisClass(),
                                            classRefType.getSuperClass(),
                                            classRefType.getVisibilityList(),
                                            classRefType.getPrimary());
    }
    return result;
  }

  protected Type2 lookupClass(ClassRef classRef)
  {
    Type2 result = factory().createUnknownType();
    Type refType = getType(classRef.getName());
    if (refType instanceof GenericType) {
      ZNameList names = ZUtils.assertZNameList(genericType(refType).getNameList());
      List<Type2> types = classRef.getType();
      if (names.size() == types.size()) {
        unificationEnv().enterScope();
        for (int i = 0; i < names.size(); i++) {
          unificationEnv().addGenName(names.get(i), types.get(i));
        }
        Type newType = instantiate((GenericType) refType);
        refType = newType;
        unificationEnv().exitScope();
      }
    }

    if (unwrapType(refType) instanceof PowerType) {
      PowerType powerType = (PowerType) unwrapType(refType);
      result = renameClassType(powerType.getType(), classRef.getNewOldPair());
    }
    return result;
  }

  protected Type2 unionClasses(ClassUnionExpr classUnionExpr,
                               Type2 lType, Type2 rType)
  {
    Type2 result = factory().createUnknownType();
    if (lType instanceof ClassType && rType instanceof ClassType) {
      ClassType lClassType = (ClassType) lType;
      ClassType rClassType = (ClassType) rType;

      ClassRefList classes = factory().createClassRefList();
      List<NameTypePair> stateAndAttrs = factory().list();
      Signature state = factory().createSignature();
      List<NameTypePair> attrs = factory().list();
      List<NameSignaturePair> ops = factory().list();

      //check that if there are any intersecting class references,
      //they are compatible
      for (ClassRef lClassRef : lClassType.getClasses()) {
        for (ClassRef rClassRef : rClassType.getClasses()) {
          if (ZUtils.namesEqual(lClassRef.getName(), rClassRef.getName())) {
            assert lClassRef.getType().size() == rClassRef.getType().size();
            for (int i = 0; i < lClassRef.getType().size(); i++) {
              Type2 lrType = lClassRef.getType().get(i);
              Type2 rrType = rClassRef.getType().get(i);
              UResult unified = unify(lrType, rrType);
              if (unified == FAIL) {
                Object [] params = {classUnionExpr};
                error(classUnionExpr,
                      ErrorMessage.INCOMPATIBLE_CLASSUNIONEXPR, params);
                return result;
              }
            }
          }
        }
      }

      //check that the features are compatible, and find common elements
      List<NameTypePair> lsPairs = lClassType.getState().getNameTypePair();
      List<NameTypePair> rsPairs = rClassType.getState().getNameTypePair();
      List<NameTypePair> laPairs = lClassType.getAttribute();
      List<NameTypePair> raPairs = rClassType.getAttribute();

      //gather pairs from the state
      for (NameTypePair lPair : lsPairs) {
        if (!isSelfName(lPair.getZName())) {
          NameTypePair rPair = findNameTypePair(lPair.getZName(), rsPairs);
          if (rPair != null) {
            ZUtils.insert(state.getNameTypePair(), lPair);
            ZUtils.insert(state.getNameTypePair(), rPair);
            //state.getNameTypePair().add(lPair);
            //state.getNameTypePair().add(rPair);
          }
          rPair = findNameTypePair(lPair.getZName(), raPairs);
          if (rPair != null) {
            ZUtils.insert(stateAndAttrs, lPair);
            ZUtils.insert(stateAndAttrs, rPair);
            //stateAndAttrs.add(lPair);
            //stateAndAttrs.add(rPair);
          }
        }
      }

      //gather pairs from local defs
      for (NameTypePair lPair : laPairs) {
        NameTypePair rPair = findNameTypePair(lPair.getZName(), raPairs);
        if (rPair != null) {
          ZUtils.insert(attrs, lPair);
          ZUtils.insert(attrs, rPair);
          //attrs.add(lPair);
          //attrs.add(rPair);
        }
        rPair = findNameTypePair(lPair.getZName(), rsPairs);
        if (rPair != null) {
          ZUtils.insert(stateAndAttrs, lPair);
          ZUtils.insert(stateAndAttrs, rPair);
          //stateAndAttrs.add(lPair);
          //stateAndAttrs.add(rPair);
        }
      }

      //check compatibility
      if (classUnionExpr != null) {
        checkForDuplicates(state.getNameTypePair(), classUnionExpr,
                           ErrorMessage.INCOMPATIBLE_FEATURE_IN_CLASSUNIONEXPR);
        checkForDuplicates(attrs, classUnionExpr,
                           ErrorMessage.INCOMPATIBLE_FEATURE_IN_CLASSUNIONEXPR);
        //state and local defs must also be compatible
        checkForDuplicates(stateAndAttrs, classUnionExpr,
                           ErrorMessage.INCOMPATIBLE_FEATURE_IN_CLASSUNIONEXPR);
      }

      //check compatibility of operations
      List<NameSignaturePair> loPairs = lClassType.getOperation();
      //List<NameSignaturePair> roPairs = 
    		  rClassType.getOperation();
      for (NameSignaturePair lPair : loPairs) {
        ZName lName = lPair.getZName();
        NameSignaturePair rPair = findOperation(lName, rClassType);
        if (rPair != null) {
          Signature lSig = lPair.getSignature();
          Signature rSig = rPair.getSignature();
          UResult unified = unify(lSig, rSig);
          if (unified == FAIL && classUnionExpr != null) {
            Object [] params = {lName, classUnionExpr, lSig, rSig};
            error(classUnionExpr,
                  ErrorMessage.INCOMPATIBLE_OP_IN_CLASSUNIONEXPR, params);
          }
          else {
            ops.add(lPair);
          }
        }
      }

      //add the class references
      for (ClassRef classRef : lClassType.getClasses()) {
        if (!contains(classes, classRef)) {
          classes.add(classRef);
        }
      }
      for (ClassRef classRef : rClassType.getClasses()) {
        if (!contains(classes, classRef)) {
          classes.add(classRef);
        }
      }
      result = factory().createClassUnionType(classes, state, attrs, ops);
    }
    return result;
  }

  //calculate a class type from the class references in a class type
  protected Type2 resolveClassType(Type2 type)
  {
    Type2 result = type;
    if (type instanceof ClassUnionType && sectTypeEnv().getSecondTime()) {
      ClassUnionType cuType = (ClassUnionType) type;
      List<ClassRef> classes = cuType.getClasses();

      //if this is the set \oid
      if (classes.size() != 0) {
        assert classes.size() > 1;
        Type2 firstType = lookupClass(classes.get(0));
        Type2 secondType = lookupClass(classes.get(1));
        Type2 unioned = unionClasses(null, firstType, secondType);
        for (int i = 2; i < classes.size(); i++) {
          Type2 nextType = lookupClass(classes.get(0));
          unioned = unionClasses(null, unioned, nextType);
        }
        result = unioned;
      }
    }
    else if (type instanceof VariableClassType) {
      VariableClassType vClassType = (VariableClassType) type;
      if (vClassType.getValue() != vClassType) {
        result = resolveClassType(vClassType.getValue());
      }
      else if (vClassType.getCandidateType() != null) {
        result = resolveClassType(vClassType.getCandidateType());
      }
    }
    else if (type instanceof ClassType && sectTypeEnv().getSecondTime()) {
      ClassRef classRef = null;
      if (type instanceof ClassRefType) {
        ClassRefType classRefType = (ClassRefType) type;
        classRef = classRefType.getThisClass();
      }
      else if (type instanceof ClassPolyType) {
        ClassPolyType classPolyType = (ClassPolyType) type;
        classRef = classPolyType.getRootClass();
      }
      result = lookupClass(classRef);
    }
    else if (type instanceof UnknownType && sectTypeEnv().getSecondTime()) {
      result = resolveUnknownType(type);
    }
    return result;
  }

  protected ClassRef renameClassRef(ClassRef classRef,
                                    List<NewOldPair> renamePairs)
  {
    List<NewOldPair> newClassRefPairs = factory().list();
    for (NewOldPair pair : classRef.getNewOldPair()) {
      NewOldPair newPair = factory().createNewOldPair(pair);
      newClassRefPairs.add(newPair);
    }
    for (NewOldPair renamePair : renamePairs) {
      boolean renamed = false;
      for (NewOldPair classRefPair : newClassRefPairs) {
        Name classRefNewName = classRefPair.getNewName();
        Name renameOldName = renamePair.getOldName();
        if (ZUtils.namesEqual(classRefNewName, renameOldName)) {
          classRefPair.setNewName(renamePair.getNewName());
          renamed = true;
        }
      }
      if (!renamed) {
        newClassRefPairs.add(renamePair);
      }
    }
    ClassRef result =
      factory().createClassRef(classRef.getName(),
                               classRef.getType(),
                               newClassRefPairs);
    return result;
  }

  protected CarrierSet getCarrierSet()
  {
    return new net.sourceforge.czt.typecheck.oz.util.CarrierSet(true);
  }

  public String toString(Type type)
  {
    String result = new String();
    if (unwrapType(type) instanceof PowerType) {
      PowerType powerType = (PowerType) unwrapType(type);
      result = "P " + exprChecker().toString(powerType.getType());
    }
    else if (type instanceof net.sourceforge.czt.oz.ast.ClassRefType) {
      ClassRefType ctype = (ClassRefType) type;
      result = classRefTypeToString(ctype);
    }
    else if (type instanceof ClassUnionType ||
             type instanceof ClassPolyType)
    {
      ClassType cType = (ClassType) type;
      result += type.toString();
      result += "\n";
      result += toString(cType);
    }
    else {
      result = type.toString();
    }
    return result;
  }

  public String classRefTypeToString(ClassRefType ctype)
  {
    String result = new String();
    Name className = ctype.getThisClass().getName();
    result += "(CLASS " + className + "\n";

    result += "\tREF(" + ctype.getClasses() + ")\n";
    result += "\tATTR(" + className + ")\n";
    for (Object o : ctype.getAttribute()) {
      NameTypePair pair = (NameTypePair) o;
      result += "\t\t" + pair.getZName() + " : " + pair.getType() + "\n";
    }
    result += "\tSTATE(" + className + ")\n";
    for (Object o : ctype.getState().getNameTypePair()) {
      NameTypePair pair = (NameTypePair) o;
      result += "\t\t" + pair.getZName() + " : " + toString(pair.getType()) + "\n";
    }
    result += "\tOPS(" + className + ")\n";
    for (Object o : ctype.getOperation()) {
      NameSignaturePair p = (net.sourceforge.czt.oz.ast.NameSignaturePair) o;
      result += "\t\t" + p.getZName() + " : " + p.getSignature() + "\n";
    }
    result += ")";
    return result;
  }

  public String toString(ClassRefType ctype)
  {
    String result = new String();
    result += "(CLASSTYPE " + ctype.getThisClass() + "\n";
    result += "\tSUPER(";
    for (ClassRef classRef :  ctype.getSuperClass()) {
      result += classRef + " ";
    }
    result += ")\n";
    result += "\tREF(\n";
    for (ClassRef classRef :  ctype.getClasses()) {
      result += "\t\t" + classRef + "\n";
    }
    result += ")\n";
    result += "\tATTR\n";
    for (NameTypePair pair : ctype.getAttribute()) {
      result += "\t\t" + pair.getZName() + " : " + pair.getType() + "\n";
    }
    result += ")\n";
    result += "\tSTATE\n";
    for (NameTypePair pair : ctype.getState().getNameTypePair()) {
      result += "\t\t" + pair.getZName() + " : " + toString(pair.getType()) + "\n";
    }
    result += "\tOPS\n";
    for (NameSignaturePair pair : ctype.getOperation()) {
      result += "\t\t" + pair.getZName() + " : " + pair.getSignature() + "\n";
    }
    result += ")";
    return result;    
  }
}
