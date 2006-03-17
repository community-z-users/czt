/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

import java.io.Writer;
import java.io.StringWriter;
import java.util.List;
import java.util.Iterator;
import java.util.logging.Logger;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract public class Checker<R>
  implements TermVisitor<R>
{
  //the information required for the typechecker classes.
  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    typeChecker_ = typeChecker;
  }

  /**
   * Double check that this visitor is not being asked to visit a
   * non-Decl object.
   */
  public R visitTerm(Term term)
  {
    String position = position((TermA) term);
    logger().warning(this.getClass().getName() +
                     " being asked to visit " +
                     term.getClass().getName() +
                     " at location " + position);
    return null;
  }

  //adds a type annotation created from a type to a TermA
  protected void addTypeAnn(TermA termA, Type type)
  {
    assert type != null;
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);
    if (typeAnn == null) {
      typeAnn = factory().createTypeAnn(type);
      termA.getAnns().add(typeAnn);
    }
    else {
      typeAnn.setType(type);
    }
  }

  //adds a signature annotation create from a signature to a TermA
  protected void addSignatureAnn(TermA termA, Signature signature)
  {
    assert signature != null;
    SignatureAnn signatureAnn =
      (SignatureAnn) termA.getAnn(SignatureAnn.class);
    if (signatureAnn == null) {
      signatureAnn = factory().createSignatureAnn(signature);
      termA.getAnns().add(signatureAnn);
    }
    else {
      Signature oldSignature = (Signature) signatureAnn.getSignature();
      if (oldSignature instanceof VariableSignature &&
          variableSignature(oldSignature).getValue() == oldSignature) {
        variableSignature(oldSignature).setValue(signature);
      }
      else {
        signatureAnn.setSignature(signature);
      }
    }
  }

  protected TypeAnn getTypeAnn(TermA termA)
  {
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);
    if (typeAnn == null) {
      typeAnn = factory().createTypeAnn();
      addAnn(termA, typeAnn);
    }
    return typeAnn;
  }

  protected Type2 getType2FromAnns(TermA termA)
  {
    Type annType = getTypeFromAnns(termA);
    Type2 result = unwrapType(annType);
    return result;
  }

  protected Type getTypeFromAnns(TermA termA)
  {
    Type result = factory().createUnknownType();
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn != null) {
      result = typeAnn.getType();
    }
    return result;
  }

  //add an error to the list of error annotation
  protected void error(ErrorAnn errorAnn)
  {
    paraErrors().add(errorAnn);
  }

  //add an error as an annotation to the term. Return true if and only
  //if this error is not already added to this term
  protected boolean addErrorAnn(TermA termA, ErrorAnn errorAnn)
  {
    for (Object ann : termA.getAnns()) {
      if (ann instanceof ErrorAnn) {
        ErrorAnn existingAnn = (ErrorAnn) ann;
        if (errorAnn.getErrorMessage().equals(existingAnn.getErrorMessage())) {
          return false;
        }
      }
    }
    termA.getAnns().add(errorAnn);
    return true;
  }

  //add an error to the list of error messages, and as an annotation to the term
  protected void error(TermA termA, ErrorAnn errorAnn)
  {
    boolean added = addErrorAnn(termA, errorAnn);
    if (added) error(errorAnn);
  }

  protected void error(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = errorAnn(termA, error, params);
    error(termA, errorAnn);
  }

  protected void error(TermA termA, String error, Object [] params)
  {
    ErrorAnn errorAnn = errorAnn(termA, error, params);
    error(termA, errorAnn);
  }

  protected ErrorAnn errorAnn(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = exprChecker().errorAnn(termA, error.toString(), params);
    return errorAnn;
  }

  protected ErrorAnn errorAnn(TermA termA, String error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
                                     sectName(), nearestLocAnn(termA),
                                     termA, markup());
    return errorAnn;
  }

  protected void removeError(TermA termA)
  {
    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object ann = iter.next();
      if (ann instanceof ErrorAnn) {
        iter.remove();
        paraErrors().remove(ann);
      }
    }
  }

  //converts a Term to a string
  protected String format(Term term)
  {
    try {
      Term newTerm = (Term) term.accept(exprChecker().getCarrierSet());
      StringWriter writer = new StringWriter();
      print(newTerm, writer, sectInfo(), sectName(), markup());
      return writer.toString();
    }
    catch (Exception e) {
      String message = "Cannot be printed";
      e.printStackTrace();
      return message;
    }
  }

  protected CarrierSet getCarrierSet()
  {
    return new CarrierSet();
  }

  protected void print(Term term,
                       Writer writer,
                       SectionInfo sectInfo,
                       String sectName,
                       Markup markup)
  {
    PrintUtils.print(term, writer, sectInfo, sectName, markup());
  }

  //get the position of a TermA from its annotations
  protected String position(TermA termA)
  {
    String result = "Unknown location: ";

    LocAnn locAnn = nearestLocAnn(termA);
    if (locAnn != null) {
      result = "\"" + locAnn.getLoc() + "\", ";
      result += "line " + locAnn.getLine() + ": ";
    }
    else {
      result = "No location information";
    }

    return result;
  }

  //find the closest LocAnn
  protected LocAnn nearestLocAnn(TermA termA)
  {
    LocAnn result = (LocAnn) termA.getAnn(LocAnn.class);

    if (result == null) {
      for (int i = 0; i < termA.getChildren().length; i++) {
        Object next = termA.getChildren()[i];
        if (next instanceof TermA) {
          LocAnn nextLocAnn = nearestLocAnn((TermA) next);
          return nextLocAnn;
        }
      }
    }
    return result;
  }

  protected UResult unify(Type2 typeA, Type2 typeB)
  {
    return unificationEnv().unify(typeA, typeB);
  }

  protected UResult unify(Signature sigA, Signature sigB)
  {
    return unificationEnv().unify(sigA, sigB);
  }

  public UResult strongUnify(Type2 typeA, Type2 typeB)
  {
    return unificationEnv().strongUnify(typeA, typeB);
  }

  protected CarrierSet carrierSet()
  {
    return typeChecker_.carrierSet_;
  }

  //a Factory for creating Z terms
  protected Factory factory()
  {
    return typeChecker_.zFactory_;
  }

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv()
  {
    return typeChecker_.sectTypeEnv_;
  }

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv()
  {
    return typeChecker_.typeEnv_;
  }

  //the TypeEnv for pending global declarations
  protected TypeEnv pending()
  {
    return typeChecker_.pending_;
  }

  //true if and only if the previous type lookup came from the pending
  //environment
  protected boolean isPending()
  {
    return typeChecker_.isPending_;
  }

  protected void setIsPending(boolean isPending)
  {
    typeChecker_.isPending_ = isPending;
  }

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv()
  {
    return typeChecker_.unificationEnv_;
  }

  //a section manager
  protected SectionInfo sectInfo()
  {
    return typeChecker_.sectInfo_;
  }

  //the markup
  protected Markup markup()
  {
    return typeChecker_.markup_;
  }

  //set the markup for printing error messages
  protected void setMarkup(Markup markup)
  {
    typeChecker_.markup_ = markup;
  }

  //set the markup from the LocAnn of a term, using LATEX if the
  //markup cannot be determined from the location
  protected void setMarkup(TermA termA)
  {
    LocAnn locAnn = (LocAnn) termA.getAnn(LocAnn.class);
    if (locAnn != null) {
      String fileName = locAnn.getLoc();
      Markup markup = ParseUtils.getMarkup(fileName);
      setMarkup(markup == null ? Markup.LATEX : markup);
    }
  }

  //the current section name
  protected String sectName()
  {
    return typeChecker_.sectName_.toString();
  }

  //set the current section name
  protected void setSectName(String sectName)
  {
    typeChecker_.sectName_.replace(0, typeChecker_.sectName_.length(),
                                   sectName);
  }

  //the list of errors thrown by retrieving type info
  protected List<ErrorAnn> errors()
  {
    return typeChecker_.errors_;
  }

  //the list of errors thrown by retrieving type info
  protected List<Object> paraErrors()
  {
    return typeChecker_.paraErrors_;
  }

  protected boolean useBeforeDecl()
  {
    return typeChecker_.useBeforeDecl_;
  }

  protected int id()
  {
    return typeChecker_.id_++;
  }

  //the logger instance
  protected Logger logger()
  {
    return typeChecker_.logger_;
  }

  //the visitors used to typechecker a spec
  protected Checker<Object> specChecker()
  {
    return typeChecker_.specChecker_;
  }

  protected Checker<Signature> paraChecker()
  {
    return typeChecker_.paraChecker_;
  }

  protected Checker<List<NameTypePair>> declChecker()
  {
    return typeChecker_.declChecker_;
  }

  protected Checker<Type2> exprChecker()
  {
    return typeChecker_.exprChecker_;
  }

  protected Checker<UResult> predChecker()
  {
    return typeChecker_.predChecker_;
  }

  protected Checker<Signature> schTextChecker()
  {
    return typeChecker_.schTextChecker_;
  }

  protected Checker<? extends ErrorAnn> postChecker()
  {
    return typeChecker_.postChecker_;
  }

  protected Checker<List<Type2>> charTupleChecker()
  {
    return typeChecker_.charTupleChecker_;
  }

  protected void postCheck()
  {
    //post-check any previously unresolved expressions
    List<ErrorAnn> paraErrors = factory().list();
    for (Object next : paraErrors()) {
      if (next instanceof TermA) {
        TermA termA = (TermA) next;
        ErrorAnn errorAnn = termA.accept(postChecker());
        if (errorAnn != null) {
          paraErrors.add(errorAnn);
        }
      }
      else if (next instanceof ErrorAnn) {
        ErrorAnn errorAnn = (ErrorAnn) next;
        paraErrors.add(errorAnn);
      }
    }
    paraErrors().clear();
    errors().addAll(paraErrors);
  }

  protected boolean checkPair(NameTypePair first,
                              NameTypePair second,
                              List<TermA> termList,
                              String errorMessage)
  {
    boolean result = true;
    Type2 firstType = unwrapType(first.getType());
    Type2 secondType = unwrapType(second.getType());
    UResult unified = unify(firstType, secondType);

    //if the types don't agree, raise an error
    if (unified == FAIL) {
      result = false;
      //terms are not printed in some error messages
      if (termList.size() > 0) {
        List<Object> params = factory().list();
        params.add(second.getZDeclName());
        params.addAll(termList);
        params.add(firstType);
        params.add(secondType);
        error(termList.get(0), errorMessage, params.toArray());
      }
      else {
        Object [] params =
          new Object [] {second.getZDeclName(), firstType, secondType};
        error(second.getZDeclName(), errorMessage, params);
      }
    }
    return result;
  }

  protected void insertUnsort(List<NameTypePair> pairsA,
                              List<NameTypePair> pairsB)
  {
    for (NameTypePair pair : pairsB) {
      insertUnsort(pairsA, pair);
    }
  }

  protected void insertUnsort(List<NameTypePair> pairsA, NameTypePair pair)
  {
    for (NameTypePair pairA : pairsA) {
      if (namesEqual(pairA.getZDeclName(), pair.getZDeclName())) {
        checkPair(pairA, pair, factory().<TermA>list(),
                  ErrorMessage.TYPE_MISMATCH_IN_SIGNATURE.toString());
        return;
      }
    }
    pairsA.add(pair);
  }

  //precondition: pairsA is sorted
  protected void insertSort(List<NameTypePair> pairsA,
                            List<NameTypePair> pairsB,
                            TermA termA)
  {
    insertSort(pairsA, pairsA, factory().list(termA),
               ErrorMessage.TYPE_MISMATCH_IN_SIGNATURE.toString());
  }

  //precondition: pairsA is sorted
  protected void insertSort(List<NameTypePair> pairsA,
                               List<NameTypePair> pairsB,
                               List<TermA> termList,
                               String errorMessage)
  {
    for (NameTypePair pair : pairsB) {
      insertSort(pairsA, pair, termList, errorMessage);
    }
  }

  //precondition: pairs is sorted
  protected void insertSort(List<NameTypePair> pairs,
                            NameTypePair pair,
                            List<TermA> termList,
                            String errorMessage)
  {
    int i = 0;
    while (i < pairs.size() &&
           compareTo(pairs.get(i).getZDeclName(), pair.getZDeclName()) < 0) {
      i++;
    }

    if (namesEqual(pairs.get(i).getZDeclName(), pair.getZDeclName())) {
      checkPair(pairs.get(i), pair, termList, errorMessage);
    }
    else {
      pairs.add(i, pair);
    }
  }

  protected void checkForDuplicates(List<NameTypePair> pairs,
                                    TermA termA)
  {
    checkForDuplicates(pairs, termA,
                       ErrorMessage.TYPE_MISMATCH_IN_SIGNATURE.toString());
  }

  //check for type mismatches in a list of decls. Add an ErrorAnn to
  //any name that is in error
  protected void checkForDuplicates(List<NameTypePair> pairs,
                                    TermA termA,
                                    String errorMessage)
  {
    List<TermA> termList = factory().list();
    if (termA != null) {
      termList.add(termA);
    }
    checkForDuplicates(pairs, termList, errorMessage);
  }

  //check for type mismatches in a list of decls. Add an ErrorAnn to
  //any name that is in error
  protected void checkForDuplicates(List<NameTypePair> pairs,
                                    List<TermA> termList,
                                    String errorMessage)
  {
    for (int i = 0; i < pairs.size(); i++) {
      NameTypePair first = pairs.get(i);
      for (int j = i + 1; j < pairs.size(); j++) {
        NameTypePair second = pairs.get(j);
        if (namesEqual(first.getZDeclName(), second.getZDeclName())) {
          Type2 firstType = unwrapType(first.getType());
          Type2 secondType = unwrapType(second.getType());
          UResult unified = unify(firstType, secondType);

          //if the types don't agree, raise an error
          if (unified == FAIL) {
            //terms are not printed in some error messages
            if (termList.size() > 0) {
              List<Object> params = factory().list();
              params.add(second.getZDeclName());
              params.addAll(termList);
              params.add(firstType);
              params.add(secondType);
              error(termList.get(0), errorMessage, params.toArray());
            }
            else {
              Object [] params =
                new Object [] {second.getZDeclName(), firstType, secondType};
              error(second.getZDeclName(), errorMessage, params);
            }
          }
          //we don't need the second declaration, so merge the IDs
          second.getZDeclName().setId(first.getZDeclName().getId());
          //          pairs.remove(j--);
        }
      }
    }
  }

  //construct the declarations from a variable declaration if there
  //are no typing errors, otherwise, raise the errors
  protected List<NameTypePair> checkVarDecl(VarDecl varDecl,
                                            UResult unified,
                                            Type2 exprType,
                                            PowerType vPowerType)
  {
    //the list of name type pairs in this VarDecl
    List<NameTypePair> pairs = factory().list();

    //if the type is not a power type, raise an error
    if (unified == FAIL) {
      Expr expr = varDecl.getExpr();
      Object [] params = {expr, exprType};
      error(expr, ErrorMessage.NON_SET_IN_DECL, params);
    }
    //otherwise, create the list of name/type pairs
    else {
      Type2 baseType = null;
      //if use-before-decl is switched on and the expr is undeclared,
      //then set IsMem to true
      if (useBeforeDecl() && exprType instanceof UnknownType){
        UnknownType uType = (UnknownType) exprType;
        if (uType.getZRefName() != null) {
          uType.setIsMem(true);
        }
        baseType = uType;
      }
      //otherwise, the type of the variable is the base type of the expr
      else {
        baseType = vPowerType.getType();
      }

      //get the DeclNames
      List<DeclName> declNames = varDecl.getDeclName();
      for (DeclName declName : declNames) {
        //add a unique ID to this name
        factory().addDeclNameID(declName);

        //add the name and its type to the list of NameTypePairs
        NameTypePair pair = factory().createNameTypePair(declName, baseType);
        pairs.add(pair);
      }
    }
    return pairs;
  }

  protected Signature createCompSig(Signature lSig, Signature rSig,
                                    TermA termA, String errorMessage)
  {
    //b3 and b4 correspond to the variable names "\Beta_3" and
    //"\Beta_4" in the standard
    List<NameTypePair> b3Pairs = factory().list(lSig.getNameTypePair());
    List<NameTypePair> b4Pairs = factory().list(rSig.getNameTypePair());
    List<NameTypePair> rPairs = rSig.getNameTypePair();
    for (NameTypePair rPair : rPairs) {
      ZDeclName rName = rPair.getZDeclName();

      //if the name + nextstoke is in lSig, remove it from b3, and
      //remove name from b4
      List<Stroke> strokes = factory().list(rName.getStroke());
      int size = strokes.size();
      strokes.add(factory().createNextStroke());
      ZDeclName sName = factory().createZDeclName(rName.getWord(), strokes);
      NameTypePair foundPair = findNameTypePair(sName, lSig);
      if (foundPair != null) {
        Type2 fType = unwrapType(foundPair.getType());
        Type2 rType = unwrapType(rPair.getType());
        UResult unified = unify(fType, rType);
        if (unified == FAIL) {
          Object [] params = {termA, sName, fType, rName, rType};
          error(termA, errorMessage, params);
        }
        removeObject(b3Pairs, foundPair);
        removeObject(b4Pairs, rPair);
      }
    }
    b3Pairs.addAll(b4Pairs);
    Signature result = factory().createSignature(b3Pairs);
    return result;
  }

  protected Signature createPipeSig(Signature lSig, Signature rSig,
                                    TermA termA, String errorMessage)
  {
    //b3 and b4 correspond to the variable names "\Beta_3" and
    //"\Beta_4" in the standard
    List<NameTypePair> b3Pairs = factory().list(lSig.getNameTypePair());
    List<NameTypePair> b4Pairs = factory().list(rSig.getNameTypePair());
    List<NameTypePair> rPairs = rSig.getNameTypePair();
    for (NameTypePair rPair : rPairs) {
      ZDeclName rName = rPair.getZDeclName();
      List<Stroke> strokes = factory().list(rName.getStroke());
      int size = strokes.size();
      if (size > 0 && strokes.get(size - 1) instanceof InStroke) {
        OutStroke out = factory().createOutStroke();
        strokes.set(size - 1, out);
        ZDeclName sName = factory().createZDeclName(rName.getWord(), strokes);
        NameTypePair foundPair = findNameTypePair(sName, lSig);
        if (foundPair != null) {
          Type2 fType = unwrapType(foundPair.getType());
          Type2 rType = unwrapType(rPair.getType());
          UResult unified = unify(fType, rType);
          if (unified == FAIL) {
            Object [] params = {termA, sName, fType, rName, rType};
            error(termA, errorMessage, params);
          }
          removeObject(b3Pairs, foundPair);
          removeObject(b4Pairs, rPair);
        }
      }
    }
    //create the signature
    b3Pairs.addAll(b4Pairs);
    Signature result = factory().createSignature(b3Pairs);
    return result;
  }

  protected Signature createHideSig(Signature signature,
                                    List<RefName> refNames, TermA termA)
  {
    //create a new name/type pair list
    List<NameTypePair> pairs = signature.getNameTypePair();
    List<NameTypePair> newPairs = factory().list(pairs);

    //iterate over every name, removing it from the signature
    for (RefName refName : refNames) {
      ZRefName zRefName = assertZRefName(refName);
      ZDeclName zDeclName = factory().createZDeclName(zRefName);
      NameTypePair rPair = findNameTypePair(zDeclName, signature);

      //if this is name is not in the schema, raise an error
      if (rPair == null) {
        Object [] params = {termA, zDeclName};
        error(termA, ErrorMessage.NON_EXISTENT_NAME_IN_HIDEEXPR, params);
      }
      //if it is in the schema, remove it
      else {
        for (Iterator pIter = newPairs.iterator(); pIter.hasNext(); ) {
          NameTypePair nPair = (NameTypePair) pIter.next();
          if (nPair == rPair) {
            pIter.remove();
          }
        }
      }
    }
    Signature result = factory().createSignature(newPairs);
    return result;
  }

  //check for duplicate names in a list of renames
  protected void checkForDuplicateRenames(List<NewOldPair> renamePairs,
                                          TermA termA, String errorMessage)
  {
    //first check for duplicate renames
    List<ZRefName> oldNames = factory().list();
    for (NewOldPair pair : renamePairs) {
      ZRefName oldName = pair.getZRefName();
      //if the old name is duplicated, raise an error
      if (oldNames.contains(oldName)) {
        Object [] params = {termA, oldName};
        error(termA, errorMessage, params);
      }
      oldNames.add(oldName);
    }
  }

  //return a list with the rename pairs in 'sources' merged with
  //'targets', renaming any transitive renames
  protected List<NewOldPair> mergeRenamePairs(List<NewOldPair> targets,
                                              List<NewOldPair> sources)
  {
    List<NewOldPair> result = factory().list();
    for (NewOldPair pair : targets) {
      NewOldPair newPair = factory().createNewOldPair(pair);
      result.add(newPair);
    }
    for (NewOldPair source : sources) {
      boolean renamed = false;
      for (NewOldPair target : result) {
        DeclName targetNewName = target.getNewName();
        RefName sourceOldName = source.getOldName();
        if (namesEqual(targetNewName, sourceOldName)) {
          target.setNewName(source.getNewName());
          renamed = true;
        }
      }
      if (!renamed && !targets.contains(source)) {
        targets.add(source);
      }
    }
    return result;
  }

  //add IDs to each new name in a list of renaming pairs
  protected void addDeclNameIDs(List<NewOldPair> pairs)
  {
    for (NewOldPair pair : pairs) {
      factory().addDeclNameID(pair.getNewName());
    }
  }

  //make a tuple from a sequence (section 9.2 of the Z standard)
  protected Type2 mkTuple(List<Type2> list)
  {
    assert list.size() > 0;
    Type2 result = list.size() == 1 ?
      list.get(0) :
      factory().createProdType(list);
    return result;
  }

  //rename the declarations
  protected Signature rename(Signature signature, List<NewOldPair> renamePairs)
  {
    List<NameTypePair> newPairs = factory().list();
    List<NameTypePair> pairs = signature.getNameTypePair();
    for (NameTypePair pair : pairs) {
      NewOldPair namePair = findNewOldPair(pair.getZDeclName(), renamePairs);
      if (namePair != null) {
        ZDeclName newName = namePair.getZDeclName();
        NameTypePair newPair =
          factory().createNameTypePair(newName, pair.getType());
        newPairs.add(newPair);
      }
      else {
        newPairs.add(pair);
      }
    }
    Signature result = factory().createSignature(newPairs);
    return result;
  }

  protected Signature createRenameSig(Signature signature,
                                      List<NewOldPair> renamePairs,
                                      TermA termA, String errorMessage)
  {
    checkForDuplicateRenames(renamePairs, termA, errorMessage);
    Signature result = rename(signature, renamePairs);
    return result;
  }

  protected UResult checkChainRelOp(AndPred andPred)
  {
    UResult result = SUCC;

    //if this is a chain relation, unify the RHS of the left pred
    //with the LHS of the right predicate
    if (And.Chain.equals(andPred.getAnd())) {
      //get the types of the left and right preds
      Pred leftPred = andPred.getLeftPred();
      Type2 rhsLeft = getRightType(leftPred);
      Pred rightPred = andPred.getRightPred();
      Type2 lhsRight = getLeftType(rightPred);

      //if the lhs and rhs do not unify, raise an error
      UResult unified = unify(rhsLeft, lhsRight);
      if (unified == FAIL) {
        Object [] params = {andPred, rhsLeft, lhsRight};
        error(andPred, ErrorMessage.TYPE_MISMATCH_IN_CHAIN_REL, params);
        result = FAIL;
      }
      else if (unified == PARTIAL) {
        result = PARTIAL;
      }
    }
    return result;
  }

  protected Type2 getLeftType(Pred pred)
  {
    MemPred memPred = (MemPred) pred;
    List<Type2> types = getLeftRightType(memPred);
    Type2 result = types.get(0);
    return result;
  }

  protected Type2 getRightType(Pred pred)
  {
    Type2 result = null;

    if (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      List<Type2> types = getLeftRightType(memPred);
      result = types.get(1);
    }
    else if (pred instanceof AndPred) {
      AndPred andPred = (AndPred) pred;
      MemPred memPred = (MemPred) andPred.getRightPred();
      result = getRightType(memPred);
    }

    return result;
  }

  protected List<Type2> getLeftRightType(MemPred memPred)
  {
    List<Type2> result = factory().list();

    Expr leftExpr = memPred.getLeftExpr();
    Expr rightExpr = memPred.getRightExpr();

    //if this pred is an equality
    boolean mixfix = memPred.getMixfix().booleanValue();
    if (mixfix && rightExpr instanceof SetExpr) {
      result.add(getType2FromAnns(leftExpr));
      result.add(getBaseType(getType2FromAnns(rightExpr)));
    }
    //if this is a membership
    else if (!mixfix) {
      result.add(getType2FromAnns(leftExpr));
      result.add(getType2FromAnns(rightExpr));
    }
    //if this is a relation
    else {
      if (leftExpr instanceof TupleExpr) {
        TupleExpr tupleExpr = (TupleExpr) leftExpr;
        result.add(getType2FromAnns(tupleExpr.getZExprList().get(0)));
        result.add(getType2FromAnns(tupleExpr.getZExprList().get(1)));
      }
      else {
        result.add(getType2FromAnns(leftExpr));
      }
    }

    return result;
  }

  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown.
   */
  public Type2 getBaseType(Type2 type2)
  {
    Type2 result = factory().createUnknownType();

    //if it's a PowerType, get the base type
    if (type2 instanceof PowerType) {
      PowerType powerType = (PowerType) type2;
      result = powerType.getType();
    }
    else if (type2 instanceof UnknownType) {
      result = type2;
    }

    return result;
  }

  protected GenericType instantiate(GenericType gType)
  {
    assert gType.getOptionalType() == null;
    List<ZDeclName> zDeclNames = gType.getName();
    Type2 firstType = gType.getType();
    Type2 optionalType =
      exprChecker().instantiate(gType.getType());
    GenericType result =
      factory().createGenericType(zDeclNames, firstType, optionalType);
    return result;
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();
    if (type instanceof GenParamType) {
      GenParamType genParamType = (GenParamType) type;
      ZDeclName genName = genParamType.getName();

      //try to get the type from the UnificationEnv
      Type unificationEnvType = unificationEnv().getType(genName);

      //if this type's reference is in the parameters
      if (isPending() && containsID(typeEnv().getParameters(), genName)) {
        result = type;
      }
      else if (unificationEnvType instanceof UnknownType &&
               unknownType(unificationEnvType).getZRefName() == null) {
        VariableType vType = factory().createVariableType();
        result = vType;
        unificationEnv().addGenName(genName, result);
      }
      else if (unificationEnvType instanceof Type2) {
        result = (Type2) unificationEnvType;
      }
      else {
        assert false : "Cannot instantiate " + type;
      }
    }
    else if (type instanceof VariableType) {
      VariableType vType = (VariableType) type;
      if (vType.getValue() != vType) {
        result = exprChecker().instantiate(vType.getValue());
      }
      else {
        result = vType;
      }
    }
    else if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      Type2 replaced = exprChecker().instantiate(powerType.getType());
      result = factory().createPowerType(replaced);
    }
    else if (type instanceof GivenType) {
      GivenType givenType = (GivenType) type;
      result = factory().createGivenType(givenType.getName());
    }
    else if (type instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) type;
      Signature signature =
        exprChecker().instantiate(schemaType.getSignature());
      result = factory().createSchemaType(signature);
    }
    else if (type instanceof ProdType) {
      ProdType prodType = (ProdType) type;
      List<Type2> newTypes =
        exprChecker().instantiateTypes(prodType.getType());
      result = factory().createProdType(newTypes);
    }
    else if (type instanceof UnknownType) {
      UnknownType uType = (UnknownType) type;
      ZRefName uTypeName = uType.getZRefName();
      if (uTypeName != null) {
        ParameterAnn pAnn = (ParameterAnn) uTypeName.getAnn(ParameterAnn.class);
        List<Type2> types = uType.getType();
        if (pAnn != null && types.size() == 0) {
          types.addAll(pAnn.getParameters());
        }
        boolean isMem = uType.getIsMem();
        List<Type2> newTypes = exprChecker().instantiateTypes(types);
        List<NewOldPair> newPairs = factory().list(uType.getPairs());
        result = factory().createUnknownType(uTypeName, isMem, newTypes, newPairs);
      }
      else {
        result = uType;
      }
    }
    return result;
  }

  protected Signature instantiate(Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    List<NameTypePair> newPairs =
      exprChecker().instantiatePairs(pairs);
    Signature result = factory().createSignature(newPairs);
    return result;
  }

  protected List<NameTypePair> instantiatePairs(List<NameTypePair> pairs)
  {
    List<NameTypePair> newPairs = factory().list();
    for (NameTypePair pair : pairs) {
      if (pair.getType() instanceof GenericType) {
	newPairs.add(pair);
      }
      else {
        Type replaced =
          exprChecker().instantiate(unwrapType(pair.getType()));
        NameTypePair newPair =
          factory().createNameTypePair(pair.getZDeclName(), replaced);
        newPairs.add(newPair);
      }
    }
    return newPairs;
  }

  protected List<Type2> instantiateTypes(List<Type2> types)
  {
    List<Type2> newTypes = factory().list();
    for (Type2 type : types) {
      Type2 replaced = exprChecker().instantiate(type);
      newTypes.add(replaced);
    }
    return newTypes;
  }

  //if there are generics in the current type env, return a new
  //GenericType with this Type2 as the type
  protected Type addGenerics(Type2 type)
  {
    List<ZDeclName> params = typeEnv().getParameters();
    Type result = params.size() == 0
      ? type
      : factory().createGenericType(params, type, null);
    return result;
  }

  //add generic types from a list of DeclNames to the TypeEnv
  public void addGenParamTypes(List<DeclName> declNames)
  {
    typeEnv().addParameters(declNames);

    //add each DeclName and its type
    List<ZDeclName> names = factory().list();
    for (DeclName paramName : declNames) {
      ZDeclName zParamName = assertZDeclName(paramName);
      factory().addDeclNameID(zParamName);

      GenParamType genParamType = factory().createGenParamType(zParamName);
      PowerType powerType = factory().createPowerType(genParamType);

      //check if a generic parameter type is redeclared
      if (containsZDeclName(names, zParamName)) {
        Object [] params = {zParamName};
        error(zParamName, ErrorMessage.REDECLARED_GEN, params);
      }
      else {
        names.add(zParamName);
      }

      //add the name and type to the TypeEnv
      typeEnv().add(zParamName, powerType);
    }
  }

  //gets the type of the expression represented by a name
  protected Type getType(ZRefName zRefName)
  {
    setIsPending(false);

    //get the type from the TypeEnv
    Type type = typeEnv().getType(zRefName);

    //if the type environment did not know of this expression.
    //then ask the pending env
    if (type instanceof UnknownType) {
      type = pending().getType(zRefName);
      if (!(type instanceof UnknownType) ||
          ((type instanceof UnknownType) &&
           unknownType(type).getZRefName() != null) ){
        setIsPending(true);
      }
    }

    //if the pending environment did not know of this expression,
    //then ask the SectTypeEnv
    if (type instanceof UnknownType) {
      Type sectTypeEnvType = sectTypeEnv().getType(zRefName);
      if (!instanceOf(sectTypeEnvType, UnknownType.class)) {
        type = sectTypeEnvType;
      }
      else {
        UnknownType uType = (UnknownType) sectTypeEnvType;
        ZRefName uTypeName = uType.getZRefName();
        if (uTypeName != null && !zRefName.equals(uTypeName)) {
          type = exprChecker().resolveUnknownType(uType);
        }
      }
    }

    //if not in any of the environments, return a variable type with the
    //specified name
    if (type instanceof UnknownType &&
        unknownType(type).getZRefName() == null) {
      //add an UndeclaredAnn
      UndeclaredAnn ann = new UndeclaredAnn();
      zRefName.getAnns().add(ann);
    }
    else {
      //remove an UndeclaredAnn if there is one
      removeAnn(zRefName, UndeclaredAnn.class);
    }

    return type;
  }

  protected Type2 resolveUnknownType(Type2 type)
  {
    Type2 result = type;
    if (sectTypeEnv().getSecondTime() && type instanceof UnknownType) {
      UnknownType uType = (UnknownType) type;
      ZRefName uTypeName = uType.getZRefName();
      if (uTypeName != null) {
        Type refType = getType(uTypeName);
        if (refType instanceof GenericType) {
          List<ZDeclName> genNames = genericType(refType).getName();
          List<Type2> types = uType.getType();
          unificationEnv().enterScope();
          if (genNames.size() == types.size()) {
            for (int i = 0; i < genNames.size(); i++) {
              unificationEnv().addGenName(genNames.get(i), types.get(i));
            }
          }
          else {
            for (int i = 0; i < genNames.size(); i++) {
              unificationEnv().addGenName(genNames.get(i),
                                          factory().createVariableType());
            }
          }
          refType = exprChecker().instantiate((GenericType) refType);
          unificationEnv().exitScope();
        }

        if (uType.getIsMem() && unwrapType(refType) instanceof PowerType) {
          result = powerType(unwrapType(refType)).getType();
        }
        else if (!uType.getIsMem()) {
          result = unwrapType(refType);
        }
      }

      if (uType.getPairs().size() > 0 && result instanceof SchemaType) {
        Signature signature = schemaType(result).getSignature();
        List<NewOldPair> pairs = uType.getPairs();
        Signature newSig = createRenameSig(signature,
                                           uType.getPairs(),
                                           null, null);
        result = factory().createSchemaType(newSig);
      }
    }
    else if (sectTypeEnv().getSecondTime()) {
      if (type instanceof VariableType) {
	result = type;
      }
      else {
	Object [] newChildren = new Object [type.getChildren().length];
	for (int i = 0; i < type.getChildren().length; i++) {
	  Object child = type.getChildren()[i];
	  if (child instanceof Type2) {
	    newChildren[i] = resolveUnknownType((Type2) child);
	  }
	  else {
	    newChildren[i] = child;
	  }
	}
	result = (Type2) type.create(newChildren);
      }
    }
    return result;
  }

  //get a name/type pair corresponding with a particular name
  //return null if this name is not in the signature
  protected NameTypePair findNameTypePair(ZDeclName zDeclName,
                                          Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    NameTypePair result = findNameTypePair(zDeclName, pairs);
    return result;
  }

  protected NameTypePair findNameTypePair(ZRefName zRefName,
                                          Signature signature)
  {
    ZDeclName zDeclName = factory().createZDeclName(zRefName);
    return findNameTypePair(zDeclName, signature);
  }

  protected NewOldPair findNewOldPair(ZDeclName zDeclName,
                                      List<NewOldPair> pairs)
  {
    ZRefName zRefName = factory().createZRefName(zDeclName);
    return findNewOldPair(zRefName, pairs);
  }

  protected NewOldPair findNewOldPair(ZRefName zRefName,
                                      List<NewOldPair> pairs)
  {
    NewOldPair result = null;
    for (NewOldPair pair : pairs) {
      if (namesEqual(pair.getZRefName(), zRefName)) {
        result = pair;
        break;
      }
    }
    return result;
  }

  protected NameTypePair findNameTypePair(ZDeclName zDeclName,
                                          List<NameTypePair> pairs)
  {
    //problem with static import from GlobalDefs
    return GlobalDefs.findNameTypePair(zDeclName, pairs);
  }

  protected NameTypePair findNameTypePair(ZRefName zRefName,
                                          List<NameTypePair> pairs)
  {
    ZDeclName zDeclName = factory().createZDeclName(zRefName);
    return findNameTypePair(zDeclName, pairs);
  }

  protected void removeTypeAnns(Term term)
  {
    //remove the type annotation
    if (term instanceof TermA) {
      TermA termA = (TermA) term;
      Object ann = termA.getAnn(TypeAnn.class);
      if (ann != null) {
        removeAnn(termA, ann);
      }
    }

    //do the same for the children
    Object [] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object next = children[i];
      if (next != null && next instanceof Term) {
        removeTypeAnns((Term) next);
      }
    }
  }

  protected void removeErrorAnns(Term term)
  {
    //remove the type annotation
    if (term instanceof TermA) {
      TermA termA = (TermA) term;
      Object ann = termA.getAnn(ErrorAnn.class);
      while (ann != null) {
        removeAnn(termA, ann);
        ann = termA.getAnn(ErrorAnn.class);
      }
    }
  }

  protected void removeErrorAndTypeAnns(Term term)
  {
    //remove the type annotation
    if (term instanceof TermA) {
      TermA termA = (TermA) term;
      Object ann = termA.getAnn(TypeAnn.class);
      if (ann != null) {
        removeAnn(termA, ann);
      }
      ann = termA.getAnn(SignatureAnn.class);
      if (ann != null) {
        removeAnn(termA, ann);
      }
      ann = termA.getAnn(ErrorAnn.class);
      while (ann != null) {
        removeAnn(termA, ann);
        ann = termA.getAnn(ErrorAnn.class);
      }
    }

    //do the same for the children
    Object [] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object next = children[i];
      if (next != null && next instanceof Term) {
        removeErrorAndTypeAnns((Term) next);
      }
    }
  }

  public String toString(Type type)
  {
    return type.toString();
  }

  //print debuging info
  protected boolean debug()
  {
    return typeChecker_.debug_;
  }

  protected void setDebug(boolean b)
  {
    typeChecker_.debug_ = b;
  }

  protected void debug(String message)
  {
    if (debug()) {
      System.err.println(message);
    }
  }
}
