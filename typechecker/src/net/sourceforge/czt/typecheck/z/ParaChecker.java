package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 *
 */
class ParaChecker
  extends Checker
  implements GivenParaVisitor,
             AxParaVisitor,
             FreeParaVisitor,
             FreetypeVisitor,
             ConjParaVisitor,
             SchTextVisitor,
             ParaVisitor
{
  //the id of a declname in a generic parameter type
  protected int id = 0;

  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  /**
   * Any "left-over" paragraphs.
   */
  public Object visitPara(Para para)
  {
    return null;
  }

  //13.2.4.1
  public Object visitGivenPara(GivenPara givenPara)
  {
    debug("visiting GivenPara");

    //the list of NameTypePairs for this paras signature
    List nameTypePairs = list();

    //get each DeclName
    List declNames = givenPara.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();
      //check if there are strokes in the name
      if (declName.getStroke().size() > 0) {
        ErrorAnn message = errorFactory().strokeInGiven(declName);
        error(declName, message);
      }

      //create the type
      GivenType givenType = factory().createGivenType(declName);
      PowerType powerType = factory().createPowerType(givenType);

      //add this to the SectTypeEnv. Raise an error if this
      //name is already declared.
      if (!sectTypeEnv().add(declName, powerType)) {
        ErrorAnn message = errorFactory().redeclaredGlobalName(declName);
        error(declName, message);
      }

      //add the NameTypePair to the list for the signature
      NameTypePair nameTypePair =
        factory().createNameTypePair(declName, powerType);
      nameTypePairs.add(nameTypePair);
    }

    //add the signature as an annotation
    Signature signature = factory().createSignature(nameTypePairs);
    addSignatureAnn(givenPara, signature);

    return null;
  }

  //13.2.4.2 and 13.2.4.3
  public Object visitAxPara(AxPara axPara)
  {
    debug("visiting AxPara");

    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();

    //add the names to the local type env
    addGenParamTypes(axPara.getDeclName());

    //get and visit the SchText, which will add any declarations to
    //the SectTypeEnv
    SchText schText = axPara.getSchText();
    Signature signature = (Signature) schText.accept(this);

    //add the SchText signature as an annotation to this paragraph
    addSignatureAnn(axPara, signature);

    //exit the variable scope
    typeEnv().exitScope();

    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    //the list of NameTypePairs for this paras signature
    List nameTypePairs = list();

    //enter a new pending scope
    pending().enterScope();

    //visit each Freetype
    List freetypes = freePara.getFreetype();
    for (Iterator iter = freetypes.iterator(); iter.hasNext(); ) {
      Freetype freetype = (Freetype) iter.next();
      freetype.accept(this);
    }

    //enter a new pending scope
    pending().enterScope();

    //visit each Freetype again so that mutually recursive free types
    //can be supported
    for (Iterator iter = freetypes.iterator(); iter.hasNext(); ) {
      Freetype freetype = (Freetype) iter.next();
      nameTypePairs.addAll((List) freetype.accept(this));
    }

    //add these to the global environment
    List pairs = pending().getNameTypePair();
    for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      if (!sectTypeEnv().add(pair)) {
        ErrorAnn message = errorFactory().redeclaredGlobalName(pair.getName());
        error(pair.getName(), message);
      }
    }

    //exit both scopes
    pending().exitScope();
    pending().exitScope();

    //create the signature for this paragraph and add it as
    //an annotation
    Signature signature = factory().createSignature(nameTypePairs);
    addSignatureAnn(freePara, signature);

    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    //the list of NameTypePairs for freetype's parent's signature
    List nameTypePairs = list();

    //the type of the Freetype's DeclName is a powerset of the
    //given type of itself
    DeclName declName = freetype.getDeclName();
    GivenType givenType = factory().createGivenType(declName);
    PowerType powerType = factory().createPowerType(givenType);

    //add this to the SectTypeEnv
    NameTypePair nameTypePair =
      factory().createNameTypePair(declName, powerType);
    nameTypePairs.add(nameTypePair);

    //add the name to the pending environment
    pending().add(nameTypePair);

    //we don't visit the branches with their a "proper" visit method
    //because we need to pass the type of the DeclName
    List branches = freetype.getBranch();
    for (Iterator iter = branches.iterator(); iter.hasNext(); ) {
      Branch branch = (Branch) iter.next();
      nameTypePair = localVisitBranch(branch, givenType);
      nameTypePairs.add(nameTypePair);

      //add this pair to the SectTypeEnv
      pending().add(nameTypePair);
    }

    return nameTypePairs;
  }

  //"visit" a name type pair. We don't visit the branches with their a
  //"proper" visit method because we need to pass the type of the
  //DeclName. This method returns the name of the declaration with its
  //type
  protected NameTypePair localVisitBranch(Branch branch, GivenType givenType)
  {
    NameTypePair nameTypePair = null;

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
        ErrorAnn message = errorFactory().nonSetInFreeType(expr, exprType);
        error(expr, message);
      }
      else {
        //otherwise create the type and add it to the list of decls
        ProdType prodType =
          factory().createProdType(list(vPowerType.getType(), givenType));
        PowerType powerType =
          factory().createPowerType(prodType);
        nameTypePair = factory().createNameTypePair(declName, powerType);
      }
    }
    //if not expression, and a simple type
    else {
      nameTypePair = factory().createNameTypePair(declName, givenType);
    }

    return nameTypePair;
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

    return null;
  }

  public Object visitSchText(SchText schText)
  {
    debug("visiting SchText");

    //the list of Names declared in this schema text
    List nameTypePairs = list();

    //get and visit the list of declarations
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      nameTypePairs.addAll((List) decl.accept(declChecker()));
    }

    pending().enterScope();
    pending().add(nameTypePairs);

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
    List pairs = pending().getNameTypePair();
    exprChecker().checkForDuplicates(pairs, schText);

    //add the types from the pending environment into the the
    //SectTypeEnv
    for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      DeclName declName = pair.getName();
      Type type = addGenerics((Type2) pair.getType());
      //if the name already exists globally, raise an error
      if (!sectTypeEnv().add(declName, type)) {
        ErrorAnn message = errorFactory().redeclaredGlobalName(declName);
        error(declName, message);
      }
    }

    //exit the pending scope
    pending().exitScope();

    //the signature for this schema text
    Signature signature = factory().createSignature(nameTypePairs);

    //add this as a type annotation
    addSignatureAnn(schText, signature);

    return signature;
  }

  //if there are generics in the current type env, return a new
  //GenericType with this Type2 as the type
  protected Type addGenerics(Type2 type)
  {
    Type result = null;

    List params = typeEnv().getParameters();
    if (params.size() > 0) {
      result = factory().createGenericType(params, type, null);
    }
    else {
      result = type;
    }

    return result;
  }

  //add generic types from a list of DeclNames to the TypeEnv
  protected void addGenParamTypes(List declNames)
  {
    typeEnv().setParameters(declNames);

    //add each DeclName and its type
    List names = list();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();
      declName.setId("" + id++);

      //check if there are strokes in the name
      if (declName.getStroke().size() > 0) {
        ErrorAnn message = errorFactory().strokeInGen(declName);
        error(declName, message);
      }
      else {
        GenParamType genParamType = factory().createGenParamType(declName);
        PowerType powerType = factory().createPowerType(genParamType);

        //check if a generic parameter type is redeclared
        if (names.contains(declName.getWord())) {
          ErrorAnn message = errorFactory().redeclaredGen(declName);
          error(declName, message);
        }
        else {
          names.add(declName.getWord());
        }

        //add the name and type to the TypeEnv
        typeEnv().add(declName, powerType);
      }
    }
  }
}
