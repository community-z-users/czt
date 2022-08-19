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

import java.util.List;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;

/**
 *
 */
public class ParaChecker
  extends Checker<Signature>
  implements GivenParaVisitor<Signature>,
             AxParaVisitor<Signature>,
             FreeParaVisitor<Signature>,
             FreetypeVisitor<Signature>,
             ConjParaVisitor<Signature>,
             ZSchTextVisitor<Signature>,
             ParaVisitor<Signature>
{
  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  /**
   * Any "left-over" paragraphs.
   */
  public Signature visitPara(Para para)
  {
    Signature signature = factory().createSignature();
    return signature;
  }

  //13.2.4.1
  public Signature visitGivenPara(GivenPara givenPara)
  {
    //the list of NameTypePairs for this paras signature
    List<NameTypePair> pairs = factory().list();

    //get each ZName
    List<Name> givenNames = givenPara.getNames();
    for (Name givenName : givenNames) {
      //create the type
      ZName zGivenName = assertZName(givenName);
      factory().addNameID(zGivenName);
      GivenType givenType = factory().createGivenType(zGivenName);
      PowerType powerType = factory().createPowerType(givenType);
      paraChecker().addContext(givenType);

      //add the NameTypePair to the list for the signature
      NameTypePair pair = factory().createNameTypePair(zGivenName, powerType);
      pairs.add(pair);
    }

    //add the signature as an annotation
    Signature signature = factory().createSignature(pairs);
    addSignatureAnn(givenPara, signature);

    return signature;
  }

  //13.2.4.2 and 13.2.4.3
  /**
   * SchText typechecking within AxPara is slightly different from other SchText (e.g., within Expr or Pred).
   * In here, only generic types are added to the typeEnv() (via addGenParamTypes), whereas variables declared
   * within the schtext are added to the AxPara signature, which is later checked for duplicated add checkParaList.
   * In the case of SchTextChecker, for Expr and Pred, the situation is different: types are explicitly added to
   * the typeEnv(). Z extensions to AxPara that want to add names to the global environment, must do so through
   * an extended AxPara Signature result, rather than directly at the SchText itself.
   * @param axPara
   * @return signature of all names within this axpara.
   */
  public Signature visitAxPara(AxPara axPara)
  {
    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();

    //add the names to the local type env
    addGenParamTypes(assertZNameList(axPara.getNameList()));

    //get and visit the SchText
    SchText schText = axPara.getSchText();
    Signature signature = schText.accept(paraChecker());

    //add the SchText signature as an annotation to this paragraph
    addSignatureAnn(axPara, signature);

    //exit the variable scope
    typeEnv().exitScope();

    //REFACTOR: moved to vcg-z/feasibility
    //checkZStateInfo(axPara);

    return signature;
  }

  public Signature visitFreePara(FreePara freePara)
  {
    //the list of NameTypePairs for this paras signature
    List<NameTypePair> pairs = factory().list();

    //enter a new scope for adding the left side of each free type
    typeEnv().enterScope();
    pending().enterScope();

    //for each free type in this paragraph, first add the left side
    ZFreetypeList freetypes = assertZFreetypeList(freePara.getFreetypeList());
    for (Freetype freetype : freetypes) {
      //the type of the Freetype's ZName is a powerset of the
      //given type of itself
      ZName freeTypeName = freetype.getZName();
      factory().addNameID(freeTypeName);
      GivenType freeTypeGiven = factory().createGivenType(freeTypeName);
      PowerType powerTypeGiven = factory().createPowerType(freeTypeGiven);
      paraChecker().addContext(freeTypeGiven);

      //add this type to the local type environment for the right side
      //of the types to access, and to the signature
      pending().add(freeTypeName, powerTypeGiven);
      NameTypePair pair =
        factory().createNameTypePair(freeTypeName, powerTypeGiven);
      pairs.add(pair);
    }

    //now visit the right side of each free type
    for (Freetype freetype : freetypes) {
      Signature signature = freetype.accept(paraChecker());
      pairs.addAll(signature.getNameTypePair());
    }

    //exit the scope
    pending().exitScope();
    typeEnv().exitScope();

    //create the signature for this paragraph and add it as
    //an annotation
    Signature signature = factory().createSignature(pairs);
    addSignatureAnn(freePara, signature);

    return signature;
  }

  public Signature visitFreetype(Freetype freetype)
  {
    //the list of NameTypePairs for freetype's parent's signature
    List<NameTypePair> pairs = factory().list();

    //create the type of the left side to compose the types of the
    //branches
    ZName freeTypeName = freetype.getZName();
    factory().addNameID(freeTypeName);
    GivenType givenType = factory().createGivenType(freeTypeName);
    @SuppressWarnings("unused")
	PowerType powerType = factory().createPowerType(givenType);
    paraChecker().addContext(givenType);

    //we don't visit the branches with their a "proper" visit method
    //because we need to pass the type of the ZName
    ZBranchList branches = assertZBranchList(freetype.getBranchList());
    for (Branch branch : branches) {
      NameTypePair pair = localVisitBranch(branch, givenType);
      if (pair != null) {
        pairs.add(pair);
        //add this pair to the SectTypeEnv
        pending().add(pair);
      }
    }

    Signature signature = factory().createSignature(pairs);
    return signature;
  }

  //"visit" a freetype branch. We don't visit the branches with their
  //a "proper" visit method because we need to pass the type of the
  //Name. This method returns the name of the declaration with its
  //type
  protected NameTypePair localVisitBranch(Branch branch, GivenType givenType)
  {
    NameTypePair pair = null;
    ZName branchName = branch.getZName();
    factory().addNameID(branchName);

    //if there is an expression, then get its type and make the type of
    //this branch PowerType of the cross product of 'givenType' and the
    //expr's type (C.4.10.13)
    Expr expr = branch.getExpr();
    if (expr != null) {
      Type2 exprType = expr.accept(exprChecker());
      PowerType vPowerType = factory().createPowerType();
      UResult unified = unify(vPowerType, exprType);

      //if the expr is not a set, raise an error
      if (unified == FAIL) {
        Object [] params = {expr, exprType};
        error(expr, ErrorMessage.NON_SET_IN_FREETYPE, params);
      }
      else {
        //otherwise create the type and add it to the list of decls.
        //the type of a complex branch is a function from the type of
        //the inner expression, to the type of the lhs of the freetype
        //in which this branch is declared
        List<Type2> types = factory().list(vPowerType.getType(), givenType);
        ProdType prodType = factory().createProdType(types);
        PowerType powerType = factory().createPowerType(prodType);
        pair = factory().createNameTypePair(branchName, powerType);
      }
    }
    //if there is no expression, the type is simply the type of the
    //left side of the freetype in which this branch is declared
    else {
      pair = factory().createNameTypePair(branchName, givenType);
    }

    return pair;
  }

  public Signature visitConjPara(ConjPara conjPara)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //add the (optional) generic types
    addGenParamTypes(assertZNameList(conjPara.getNameList()));

    //visit the predicate
    Pred pred = conjPara.getPred();
    UResult solved = pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == PARTIAL) {
      pred.accept(predChecker());
    }

    //the annotation for a conjecture paragraph is an empty signature
    //unless it has a name, in which case a global name is added with 
    //an empty type. this is important to avod ducplicated theorem names    
    Signature signature = factory().createSignature();
    
    // As names are optional (and yet non-standard), if it returns null
    // just proceed as usual. Otherwise, add the name as a declared global
    // name with empty (prod?) type.
    String conjName = conjPara.getName();
    if (conjName != null)
    { 
      Name thmName = factory().createZDeclName(conjName);
      
      // empty (prod?) type for theorems, except that we add the generics
      // this may be useful for theorem provers. They will never need 
      // instantiation at the ConjPara level anyway.
      Type2 thmType2 = factory().createProdType(factory().<Type2>list());
      Type thmType = addGenerics(thmType2);
            
      NameTypePair thmPair = factory().createNameTypePair(thmName, thmType);
      signature.getNameTypePair().add(thmPair);
    }
    // conjName != null => !signature.isEmpty() = error case test is catching this. leave it out for now
    //assert (conjName == null || !signature.getNameTypePair().isEmpty()) : "named theorem has signature.";
    
    // add the (possibly non empty) signature
    addSignatureAnn(conjPara, signature);

    //exit the variable scope
    typeEnv().exitScope();

    return signature;
  }

  /**
   * This visitZSchText method is only used for schema texts related to
   * an axiomatic definition paragraph. 
   */
  public Signature visitZSchText(ZSchText zSchText)
  {
    //get and visit the list of declarations
    DeclList declList = zSchText.getDeclList();    
    List<NameTypePair> pairs = declList.accept(declChecker());
    
    //the list of Names declared in this schema text
    List<NameTypePair> gPairs = addGenerics(pairs);        
    
    pending().enterScope();
    pending().add(gPairs);

    //get and visit the pred
    Pred pred = zSchText.getPred();
    if (pred != null) {
      UResult solved = pred.accept(predChecker());
      //if the are unsolved unifications in this predicate,
      //visit it again
      if (solved == PARTIAL) {
        pred.accept(predChecker());
      }
    }

    //check that the types of duplicate names agree
    checkForDuplicates(gPairs, null);

    //exit the pending scope
    pending().exitScope();

    //the signature for this schema text
    Signature signature = factory().createSignature(gPairs);

    //add this as a type annotation
    addSignatureAnn(zSchText, signature);

    return signature;
  }
}
