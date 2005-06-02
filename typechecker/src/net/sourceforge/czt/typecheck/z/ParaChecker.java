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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 *
 */
public class ParaChecker
  extends Checker
  implements GivenParaVisitor,
             AxParaVisitor,
             FreeParaVisitor,
             FreetypeVisitor,
             ConjParaVisitor,
             SchTextVisitor,
             ParaVisitor
{
  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  /**
   * Any "left-over" paragraphs.
   */
  public Object visitPara(Para para)
  {
    Signature signature = factory().createSignature();
    return signature;
  }

  //13.2.4.1
  public Object visitGivenPara(GivenPara givenPara)
  {
    debug("visiting GivenPara");

    //the list of NameTypePairs for this paras signature
    List<NameTypePair> pairs = list();

    //get each DeclName
    List<DeclName> declNames = givenPara.getDeclName();
    for (DeclName declName : declNames) {
      //create the type
      GivenType givenType = factory().createGivenType(declName);
      PowerType powerType = factory().createPowerType(givenType);

      //add the NameTypePair to the list for the signature
      NameTypePair pair = factory().createNameTypePair(declName, powerType);
      pairs.add(pair);
    }

    //add the signature as an annotation
    Signature signature = factory().createSignature(pairs);
    addSignatureAnn(givenPara, signature);

    return signature;
  }

  //13.2.4.2 and 13.2.4.3
  public Object visitAxPara(AxPara axPara)
  {
    debug("visiting AxPara");

    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();

    //add the names to the local type env
    addGenParamTypes(axPara.getDeclName());

    //get and visit the SchText
    SchText schText = axPara.getSchText();
    Signature signature = (Signature) schText.accept(paraChecker());

    //add the SchText signature as an annotation to this paragraph
    addSignatureAnn(axPara, signature);

    //exit the variable scope
    typeEnv().exitScope();

    return signature;
  }

  public Object visitFreePara(FreePara freePara)
  {
    //the list of NameTypePairs for this paras signature
    List<NameTypePair> pairs = list();

    //enter a new pending scope
    pending().enterScope();

    //visit each Freetype
    List<Freetype> freetypes = freePara.getFreetype();
    for (Freetype freetype : freetypes) {
      freetype.accept(paraChecker());
    }

    //enter a new pending scope
    pending().enterScope();

    //visit each Freetype again so that mutually recursive free types
    //can be supported
    for (Freetype freetype : freetypes) {
      pairs.addAll((List<NameTypePair>) freetype.accept(paraChecker()));
    }

    //exit both scopes
    pending().exitScope();
    pending().exitScope();

    //create the signature for this paragraph and add it as
    //an annotation
    Signature signature = factory().createSignature(pairs);
    addSignatureAnn(freePara, signature);

    return signature;
  }

  public Object visitFreetype(Freetype freetype)
  {
    //the list of NameTypePairs for freetype's parent's signature
    List<NameTypePair> pairs = list();

    //the type of the Freetype's DeclName is a powerset of the
    //given type of itself
    DeclName declName = freetype.getDeclName();
    GivenType givenType = factory().createGivenType(declName);
    PowerType powerType = factory().createPowerType(givenType);

    //add this to the SectTypeEnv
    NameTypePair pair =
      factory().createNameTypePair(declName, powerType);
    pairs.add(pair);

    //add the name to the pending environment
    pending().add(pair);

    //we don't visit the branches with their a "proper" visit method
    //because we need to pass the type of the DeclName
    List<Branch> branches = freetype.getBranch();
    for (Branch branch : branches) {
      pair = localVisitBranch(branch, givenType);
      if (pair != null) {
        pairs.add(pair);
        //add this pair to the SectTypeEnv
        pending().add(pair);
      }
    }

    return pairs;
  }

  //"visit" a name type pair. We don't visit the branches with their a
  //"proper" visit method because we need to pass the type of the
  //DeclName. This method returns the name of the declaration with its
  //type
  protected NameTypePair localVisitBranch(Branch branch, GivenType givenType)
  {
    NameTypePair pair = null;
    DeclName declName = branch.getDeclName();

    Expr expr = branch.getExpr();
    //if there is an expression, then get its type and make the type of
    //this branch PowerType of the cross product of 'givenType' and the
    //expr's type (C.4.10.13)
    if (expr != null) {
      Type2 exprType = (Type2) expr.accept(exprChecker());

      PowerType vPowerType = factory().createPowerType();
      UResult unified = unify(vPowerType, exprType);

      //if the expr is not a set, raise an error
      if (unified == FAIL) {
        Object [] params = {expr, exprType};
        error(expr, ErrorMessage.NON_SET_IN_FREETYPE, params);
      }
      else {
        //otherwise create the type and add it to the list of decls
        ProdType prodType =
          factory().createProdType(list(vPowerType.getType(), givenType));
        PowerType powerType =
          factory().createPowerType(prodType);
        pair = factory().createNameTypePair(declName, powerType);
      }
    }
    //if not expression, and a simple type
    else {
      pair = factory().createNameTypePair(declName, givenType);
    }

    return pair;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //add the generic types
    addGenParamTypes(conjPara.getDeclName());

    //visit the predicate
    Pred pred = conjPara.getPred();
    UResult solved = (UResult) pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == PARTIAL) {
      pred.accept(predChecker());
    }

    //the annotation for a conjecture paragraph is an empty signature
    Signature signature = factory().createSignature();
    addSignatureAnn(conjPara, signature);

    //exit the variable scope
    typeEnv().exitScope();

    return signature;
  }

  public Object visitSchText(SchText schText)
  {
    debug("visiting SchText");

    //the list of Names declared in this schema text
    List<NameTypePair> pairs = list();

    //get and visit the list of declarations
    List<Decl> decls = schText.getDecl();
    for (Decl decl : decls) {
      //pairs.addAll((List<NameTypePair>) decl.accept(declChecker()));
      List<NameTypePair> dPairs = (List) decl.accept(declChecker());
      for (NameTypePair dPair : dPairs) {
        DeclName gName = dPair.getName();
        Type gType = addGenerics((Type2) dPair.getType());
        NameTypePair gPair = factory().createNameTypePair(gName, gType);
        pairs.add(gPair);
      }
    }

    pending().enterScope();
    pending().add(pairs);

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      UResult solved = (UResult) pred.accept(predChecker());

      //if the are unsolved unifications in this predicate,
      //visit it again
      if (solved == PARTIAL) {
        pred.accept(predChecker());
      }
    }

    //check that the types of duplicate names agree
    checkForDuplicates(pairs, null);

    //exit the pending scope
    pending().exitScope();

    //the signature for this schema text
    Signature signature = factory().createSignature(pairs);

    //add this as a type annotation
    addSignatureAnn(schText, signature);

    return signature;
  }
}
