package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 */
class ExprChecker
  extends Checker
  implements RefExprVisitor,
             PowerExprVisitor,
             ProdExprVisitor,
             SetExprVisitor,
             SetCompExprVisitor,
             NumExprVisitor,
             SchExprVisitor,
             TupleExprVisitor,
             TupleSelExprVisitor,
             Qnt1ExprVisitor,
             LambdaExprVisitor,
             MuExprVisitor,
             LetExprVisitor,
             SchExpr2Visitor,
             NegExprVisitor,
             CondExprVisitor,
             CompExprVisitor,
             PipeExprVisitor,
             HideExprVisitor,
             ProjExprVisitor,
             PreExprVisitor,
             ApplExprVisitor,
             ThetaExprVisitor,
             DecorExprVisitor,
             RenameExprVisitor,
             BindSelExprVisitor,
             BindExprVisitor,
             SchTextVisitor
{
  public ExprChecker(CheckerInfo info)
  {
    super(info);
  }

  public Object visitSchText(SchText schText)
  {
    //the list of Names declared in this schema text
    List nameTypePairs = list();

    //get and visit the list of declarations
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      nameTypePairs.addAll((List) decl.accept(declChecker()));
    }

    typeEnv().add(nameTypePairs);

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      UResult solved = (UResult) pred.accept(predChecker());

      //if the are unsolved unifications in this predicate,
      //visit it again
      if (PARTIAL.equals(solved)) {
        pred.accept(predChecker());
      }
    }

    //the signature for this schema text
    Signature signature = factory().createSignature(nameTypePairs);

    //add this as a type annotation
    addSignatureAnn(schText, signature);

    return signature;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    RefName refName = refExpr.getRefName();
    Type type = getType(refName);

    TypeAnn typeAnn = (TypeAnn) refExpr.getAnn(TypeAnn.class);
    List exprs = refExpr.getExpr();

    //if it is a generic type, we must instantiate the optional type
    if (isGenericType(type)) {
      GenericType genericType = (GenericType) type;

      //if the instantiation is implicit
      if (exprs.size() == 0) {
        List instantiations = list();
        unificationEnv().enterScope();

        if (typeAnn == null) {
          for (Iterator iter = genericType.getName().iterator();
               iter.hasNext(); ) {
            //get the next name and create a generic types
            DeclName declName = (DeclName) iter.next();

            if (!unificationEnv().contains(declName)) {
              //add a variable type
              VariableType vType = factory().createVariableType();
              unificationEnv().addGenName(declName, vType);
              instantiations.add(vType);
            }
          }
        }
        //instantiate the type
        instantiate(genericType);

        if (instantiations.size() > 0) {
          ParameterAnn pAnn =
            (ParameterAnn) refExpr.getAnn(ParameterAnn.class);
          if (pAnn == null) {
            pAnn = new ParameterAnn(instantiations);
          }
          refExpr.getAnns().add(pAnn);
        }

        unificationEnv().exitScope();
      }
      //if the instantiation is explicit
      else {
        if (genericType.getName().size() == exprs.size()) {
          unificationEnv().enterScope();

          if (typeAnn == null) {
            Iterator exprIter = exprs.iterator();
            for (Iterator iter = genericType.getName().iterator();
                 iter.hasNext(); ) {

              //get the next name and create a generic types
              DeclName declName = (DeclName) iter.next();

              //get the type of the next expression
              PowerType vPowerType = factory().createPowerType();

              Expr expr = (Expr) exprIter.next();
              Type2 exprType = (Type2) expr.accept(this);

              boolean unified = unify(vPowerType, exprType);
              if (unified) {
                Type2 replacementType = vPowerType.getType();

                //add the type to the environment
                unificationEnv().addGenName(declName, (Type2) replacementType);
              }
            }
          }
          //instantiate the type
          instantiate(genericType);
          unificationEnv().exitScope();
        }
      }
    }

    //add the type annotation
    addTypeAnn(refExpr, type);

    Type2 result = unwrapType(type);
    return result;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    Type type = unknownType();

    //get the expr and its type
    Expr expr = powerExpr.getExpr();
    Type2 innerType = (Type2) expr.accept(this);

    PowerType vPowerType = factory().createPowerType();
    UResult unified = unifyAux(vPowerType, innerType);

    if (FAIL.equals(unified)) {
      ErrorAnn message =
        errorFactory().nonSetInPowerExpr(powerExpr, innerType);
      error(powerExpr, message);
    }
    else {
      type = factory().createPowerType(innerType);
    }

    //add the type as an annotation
    addTypeAnn(powerExpr, type);

    return type;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    Type2 type = unknownType();

    //the list of types in the expr
    List types = list();

    //get and visit the list of expressions
    List exprs = prodExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type2 nestedType = (Type2) expr.accept(this);

      PowerType vPowerType = factory().createPowerType();
      boolean unified = unify(vPowerType, nestedType);
      if (unified) {
        types.add(vPowerType.getType());
      }
    }

    if (types.size() == exprs.size()) {
      Type2 prodType = factory().createProdType(types);
      type = factory().createPowerType(prodType);
    }

    //add the type as an annotation
    addTypeAnn(prodExpr, type);

    return type;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    //the type of a set expression is a power set of the
    //types inside the SetExpr
    Type2 innerType = factory().createVariableType();
    Type2 type = getTypeFromAnns(setExpr);
    if (isUnknownType(type)) {
      type = factory().createPowerType(innerType);
    }
    else {
      innerType = powerType(type).getType();
    }

    //get the inner expressions
    List exprs = setExpr.getExpr();

    //if the set is not empty find the inner type
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type2 exprType = (Type2) expr.accept(this);
      unify(innerType, exprType);
    }

    //add the type as an annotion
    addTypeAnn(setExpr, type);

    return type;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    //the type of a NumExpr is the given type arithmos
    DeclName declName =
      factory().createDeclName(ZString.ARITHMOS, list(), null);
    Type2 type = factory().createGivenType(declName);

    //add the type as an annotation
    addTypeAnn(numExpr, type);

    return type;
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    //visit the SchText and add return the signature
    //from that as the signature for this expression
    SchText schText = schExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);

    SchemaType schemaType = factory().createSchemaType(signature);
    PowerType type = factory().createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(schExpr, type);

    return type;
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    //the type of the overall expression
    Type2 type = unknownType();

    //enter a new variable scope
    typeEnv().enterScope();

    //get the signature from the SchText
    SchText schText = setCompExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);

    //get the expr
    Expr expr = setCompExpr.getExpr();

    //get the types from the signature
    List types = list();
    List nameTypePairs = signature.getNameTypePair();
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      Type nextType = pair.getType();
      types.add(unwrapType(nextType));
    }

    //if the expr is null, then use the signature to obtain the type
    if (expr == null) {

      //if the is only one element, then the type is a power set
      //of the type of that element
      if (types.size() == 1) {
        Type2 innerType = (Type2) types.get(0);
        type = factory().createPowerType(innerType);
      }
      //otherwise, create a ProdType
      else {
        ProdType prodType = factory().createProdType(types);
        type = factory().createPowerType(prodType);
      }
    }
    //if the expr is not null, then the overall type is a power set
    //of the type of expr
    else {
      Type2 exprType = (Type2) expr.accept(this);
      type = factory().createPowerType(exprType);
    }

    //exit the variable scope
    typeEnv().exitScope();

    //add the type annotation
    addTypeAnn(setCompExpr, type);

    return type;
  }

  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    //the individual types of the elements in the tuple
    List types = list();

    //get the types of the individual elements
    List exprs = tupleExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type innerType = (Type) expr.accept(this);
      types.add(innerType);
    }

    //create the ProdType from the list of types
    ProdType type = factory().createProdType(types);

    //add the type annotations
    addTypeAnn(tupleExpr, type);

    return type;
  }

  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    //the type of this expression
    Type2 type = unknownType();

    //get the types of the expression
    Expr expr = tupleSelExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    //if the expression is a ProdType, then find the type
    //of the selection
    if (isProdType(exprType)) {
      ProdType prodType = (ProdType) exprType;

      //get the type
      int index = tupleSelExpr.getSelect().intValue();
      if (index <= prodType.getType().size()) {
        type = (Type2) prodType.getType().get(index - 1);
      }
    }

    //add the type annotation
    addTypeAnn(tupleSelExpr, type);

    return type;
  }

  /**
   * ExistsExpr, ExistsExpr, and ForallExpr instances are
   * visited as an instance of their super class Qnt1Expr.
   * Other Qnt1Expr instances are visited by their own visit
   * methods
   */
  public Object visitQnt1Expr(Qnt1Expr qnt1Expr)
  {
    //the type of this expression
    Type2 type = unknownType();

    //visit the SchText, but do not add its declarations
    //as global
    SchText schText = qnt1Expr.getSchText();
    Signature signature = (Signature) schText.accept(this);

    Expr expr = qnt1Expr.getExpr();

    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);

    //if the type of expr is a schema, then assign the type by
    //substracting schText's signature from expr's signature
    boolean unified = unify(powerType, exprType);
    if (unified) {
      Signature qnt1ExprSignature =
        schemaHide(vSchemaType.getSignature(), signature);
      type = factory().createSchemaType(qnt1ExprSignature);
    }

    //add the type annotation
    addTypeAnn(qnt1Expr, powerType);

    return type;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    Type type = unknownType();

    //get the signature of the SchText
    SchText schText = lambdaExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);

    //get the type of the expression
    Expr expr = lambdaExpr.getExpr();
    Type exprType = (Type) expr.accept(this);

    //the characterisitic tuple of the schema text
    Type charTuple = null;

    //if the signature of the schema text is of size greater than one,
    //then the characteristic tuple is actually a tuple
    if (signature.getNameTypePair().size() > 1) {
      List charTupleList = list();

      for (Iterator iter = signature.getNameTypePair().iterator();
           iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        charTupleList.add(unwrapType(nameTypePair.getType()));
      }

      charTuple = factory().createProdType(charTupleList);
    }
    //otherwise, the characterisitic tuple is the type of the only decl
    else if (signature.getNameTypePair().size() > 0) {
      NameTypePair nameTypePair =
        (NameTypePair) signature.getNameTypePair().get(0);
      charTuple = unwrapType(nameTypePair.getType());
    }

    if (charTuple != null) {
      //the type of the expression is a power set of the cross product
      //of the characteristic tuple of the schema text, and the type of
      //the expression
      ProdType prodType =
        factory().createProdType(list(charTuple, exprType));
      type = factory().createPowerType(prodType);
    }

    //add the type annotation
    addTypeAnn(lambdaExpr, type);

    return type;
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    Type2 type = unknownType();

    //if the expr part of the expr is not null, then apply rule
    //13.9.6.12
    if (muExpr.getExpr() != null) {
      type = visitMuOrLetExpr(muExpr);
    }
    //otherwise, apply transformation rule C.6.37.2
    else {
      SchText schText = muExpr.getSchText();

      List exprList = list();
      for (Iterator iter = schText.getDecl().iterator();
           iter.hasNext(); ) {

        //for each declaration, get the name and add it to the expr
        //part of the MuExpr
        Decl decl = (Decl) iter.next();
        List decls = (List) decl.accept(declChecker());

        for (Iterator declIter = decls.iterator(); declIter.hasNext(); ) {

          NameTypePair nameTypePair = (NameTypePair) declIter.next();
          DeclName declName = nameTypePair.getName();
          RefName refName = factory().createRefName(declName.getWord(),
                                                   declName.getStroke(),
                                                   null);
          RefExpr refExpr =
            factory().createRefExpr(refName, list(), Boolean.FALSE);

          exprList.add(refExpr);
        }
      }

      //if there is more than one declaration, then the expr
      //is a tuple expr
      MuExpr transformedMuExpr = null;
      if (exprList.size() == 1) {
        Expr firstExpr = (Expr) exprList.get(0);
        transformedMuExpr = factory().createMuExpr(schText, firstExpr);
      }
      else {
        TupleExpr tupleExpr = factory().createTupleExpr(exprList);
        transformedMuExpr = factory().createMuExpr(schText, tupleExpr);
      }
      type = visitMuOrLetExpr(transformedMuExpr);
    }

    //add the type annotation
    addTypeAnn(muExpr, type);

    return type;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    Type2 type = visitMuOrLetExpr(letExpr);

    //add the type annotation
    addTypeAnn(letExpr, type);

    return type;
  }

  //a 'let' expression is easily transformed to a 'mu' expression, so
  //we visit them with  the same method
  private Type2 visitMuOrLetExpr(Expr muOrLetExpr)
  {
    //get the SchText and Expr of muOrLetExpr
    SchText schText = null;
    Expr expr = null;
    if (muOrLetExpr instanceof MuExpr) {
      MuExpr muExpr = (MuExpr) muOrLetExpr;
      schText = muExpr.getSchText();
      expr = muExpr.getExpr();
    }
    else {
      LetExpr letExpr = (LetExpr) muOrLetExpr;
      schText = letExpr.getSchText();
      expr = letExpr.getExpr();
    }

    //visit the SchText
    schText.accept(this);

    //get the type of the expression, which is also the type
    //of the entire expression (the MuExpr or LetExpr);
    Type2 type = (Type2) expr.accept(this);

    return type;
  }

  /**
   * AndExpr, OrExpr, IffExpr, and ImpliesExpr objects are visited as
   * an instance of their superclass SchExpr2. Other SchExpr2 subclass
   * instances have their own visit method
   */
  public Object visitSchExpr2(SchExpr2 schExpr2)
  {
    //the type of this expression
    Type2 type = unknownType();

    //get the types of the left and right expressions
    Expr leftExpr = schExpr2.getLeftExpr();
    Expr rightExpr = schExpr2.getRightExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);
    Type2 rightType = (Type2) rightExpr.accept(this);

    //get the element types of the expressions
    SchemaType leftSchema = factory().createSchemaType();
    PowerType leftPower = factory().createPowerType(leftSchema);

    SchemaType rightSchema = factory().createSchemaType();
    PowerType rightPower = factory().createPowerType(rightSchema);

    boolean leftUnified = unify(leftPower, leftType);
    boolean rightUnified = unify(rightPower, rightType);

    if (leftUnified && rightUnified) {

      Signature leftSig = schemaType(leftPower.getType()).getSignature();
      Signature rightSig = schemaType(rightPower.getType()).getSignature();

      if (signaturesCompatible(leftSig, rightSig)) {

        //the type is a power set of a schema that has the union of the
        //two signatures
        Signature signature = unionSignatures(leftSig, rightSig);
        SchemaType schemaType = factory().createSchemaType(signature);
        type = factory().createPowerType(schemaType);
      }
    }

    //add the type annotation
    addTypeAnn(schExpr2, type);

    return type;
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    //get the type of the expr, which is the type of the
    //overall expr
    Expr expr = negExpr.getExpr();
    Type2 type = (Type2) expr.accept(this);

    //add the type annotation
    addTypeAnn(negExpr, type);

    return type;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    Type2 type = unknownType();

    //visit the Pred
    Pred pred = condExpr.getPred();
    UResult solved = (UResult) pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (PARTIAL.equals(solved)) {
      pred.accept(predChecker());
    }

    //get the type of the left and right expr
    Expr leftExpr = condExpr.getLeftExpr();
    Expr rightExpr = condExpr.getRightExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);
    Type2 rightType = (Type2) rightExpr.accept(this);

    boolean unified = unify(leftType, rightType);
    if (unified) {
      type = leftType;
    }

    //add the type annotation
    addTypeAnn(condExpr, type);

    return type;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    Expr leftExpr = compExpr.getLeftExpr();
    Expr rightExpr = compExpr.getRightExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);
    Type2 rightType = (Type2) rightExpr.accept(this);

    //the type of this expression
    SchemaType schemaType = factory().createSchemaType();
    Type2 type = factory().createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(compExpr, type);

    return type;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    Expr leftExpr = pipeExpr.getLeftExpr();
    Expr rightExpr = pipeExpr.getRightExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);
    Type2 rightType = (Type2) rightExpr.accept(this);

    //the type of this expression
    SchemaType schemaType = factory().createSchemaType();
    Type2 type = factory().createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(pipeExpr, type);

    return type;
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    Type2 type = unknownType();

    Expr expr = hideExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);

    boolean unified = unify(powerType, exprType);
    if (unified) {
      //hide the declarations
      SchemaType schemaType = (SchemaType) powerType.getType();
      Signature signature = schemaHide(schemaType.getSignature(),
                                       hideExpr.getName());
      SchemaType hideSchemaType = factory().createSchemaType(signature);
      type = factory().createPowerType(hideSchemaType);
    }

    //add the type annotation
    addTypeAnn(hideExpr, type);

    return type;
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    //visit the left and right exprs. The type of this whole
    //expression is the type of the right expr
    Expr leftExpr = projExpr.getLeftExpr();
    Expr rightExpr = projExpr.getRightExpr();
    leftExpr.accept(this);
    Type2 type = (Type2) rightExpr.accept(this);

    //add the type annotation
    addTypeAnn(projExpr, type);

    return type;
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    //the type of this expression
    Type2 type = unknownType();

    //visit the expr
    Expr expr = preExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);

    //the type of the expression is the same a preExpr, with all
    //primed and shrieked variables hidden
    boolean unified = unify(powerType, exprType);
    if (unified) {

      SchemaType preSchemaType = schemaType(powerType.getType());
      List oldPairs = preSchemaType.getSignature().getNameTypePair();

      NextStroke nextStroke = factory().createNextStroke();
      OutStroke outStroke = factory().createOutStroke();

      //the list of NameTypePairs for the new signature
      List newPairs = list();
      for (Iterator iter = oldPairs.iterator(); iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();

        //the strokes of this name
        List strokes = nameTypePair.getName().getStroke();

        //if the last stroke is not a prime or shriek, then add
        //to the new signature
        if (strokes.size() == 0 ||
            (strokes.size() > 0 &&
             !(strokes.get(0).equals(nextStroke) ||
               strokes.get(0).equals(outStroke)))) {
          newPairs.add(nameTypePair);
        }
      }

      Signature signature = factory().createSignature(newPairs);
      SchemaType schemaType = factory().createSchemaType(signature);
      type = factory().createPowerType(schemaType);
    }

    //add the type annotation
    addTypeAnn(preExpr, type);

    return type;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    //the type of this expression
    Type2 type = unknownType();

    //get the type of the left and right expressions
    Expr funcExpr = applExpr.getLeftExpr();
    Expr argExpr = applExpr.getRightExpr();
    Type2 funcType = (Type2) funcExpr.accept(this);
    Type2 argType = (Type2) argExpr.accept(this);

    PowerType powerType = factory().createPowerType();

    unificationEnv().enterScope();

    //if the left expression is a power set of a cross product, then
    //the type of the second component is the type of the whole
    //expression
    boolean unified = unify(powerType, funcType);
    if (unified) {
      Type2 funcBaseType = powerType.getType();
      if (isProdType(funcBaseType) &&
          prodType(funcBaseType).getType().size() == 2) {

        Type2 domType = (Type2) prodType(funcBaseType).getType().get(0);

        boolean unifiedInner = unify(domType, argType);

        if (unifiedInner) {
          Type2 ranType = (Type2) prodType(funcBaseType).getType().get(1);
          type = instantiate(ranType);
          prodType(funcBaseType).getType().set(1, type);
        }
      }
    }

    unificationEnv().exitScope();

    //add the type annotation
    addTypeAnn(applExpr, type);

    return type;
  }

  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    Type2 type = unknownType();

    //visit the expr
    Expr expr = thetaExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);

    boolean unified = unify(powerType, exprType);
    if (unified) {
      type = powerType.getType();
    }

    //add the type annotation
    addTypeAnn(thetaExpr, type);

    return type;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    Type2 type = unknownType();

    //visit the expr
    Expr expr = decorExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);

    //if the expr is a schema reference, decorate each name in the
    //signature
    boolean unified = unify(powerType, exprType);
    if (unified) {
      SchemaType schemaType = (SchemaType) powerType.getType();
      SchemaType decoratedSchemaType =
        decorate(schemaType, list(decorExpr.getStroke()));
      type = factory().createPowerType(decoratedSchemaType);
    }

    //add the type annotation
    addTypeAnn(decorExpr, type);

    return type;
  }

  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    Type2 type = unknownType();

    //visit the expr
    Expr expr = renameExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);

    //if the expr is a schema reference, rename all rename pairs
    boolean unified = unify(powerType, exprType);
    if (unified) {
      SchemaType schemaType = schemaType(powerType.getType());

      List newPairs = list();
      List oldPairs = schemaType.getSignature().getNameTypePair();
      for (Iterator sIter = oldPairs.iterator(); sIter.hasNext(); ) {
        NameTypePair existingPair = (NameTypePair) sIter.next();
        DeclName existingName = existingPair.getName();

        boolean addExisting = true;
        List namePairs = renameExpr.getNameNamePair();
        for (Iterator nIter = namePairs.iterator(); nIter.hasNext(); ) {
          NameNamePair namePair = (NameNamePair) nIter.next();
          RefName oldName = namePair.getOldName();

          //if the names are equal, replace the old name with the new
          if (existingName.getWord().equals(oldName.getWord()) &&
              existingName.getStroke().equals(oldName.getStroke())) {
            DeclName newName = namePair.getNewName();
            Type newType = existingPair.getType();
            NameTypePair newPair =
              factory().createNameTypePair(newName, newType);
            newPairs.add(newPair);
            addExisting = false;
          }
        }

        //if this name was not renamed, then add the existing pair
        if (addExisting) {
          newPairs.add(existingPair);
        }
      }

      Signature newSignature = factory().createSignature(newPairs);
      SchemaType newSchemaType = factory().createSchemaType(newSignature);
      type = factory().createPowerType(newSchemaType);
    }

    //add the type annotation
    addTypeAnn(renameExpr, type);

    return type;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    Type2 type = unknownType();

    //get the type of the expression
    Expr expr = bindSelExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    SchemaType vSchemaType = factory().createSchemaType();

    //if expr is a binding, then get the type of the name
    boolean unified = unify(vSchemaType, exprType);
    if (unified) {
      SchemaType schemaType = schemaType(vSchemaType);
      RefName refName = bindSelExpr.getName();

      List nameTypePairs = schemaType.getSignature().getNameTypePair();
      for (Iterator iter = nameTypePairs.iterator();  iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        DeclName declName = nameTypePair.getName();

        if (declName.getWord().equals(refName.getWord()) &&
            declName.getStroke().equals(refName.getStroke())) {
          type = (Type2) nameTypePair.getType();
          break;
        }
      }
    }

    //add the annotation
    addTypeAnn(bindSelExpr, type);

    return type;
  }

  public Object visitBindExpr(BindExpr bindExpr)
  {
    Type2 type = unknownType();

    //the list for create the signature
    List nameTypePairs = list();

    List nameExprPairs = bindExpr.getNameExprPair();
    for (Iterator iter = nameExprPairs.iterator(); iter.hasNext(); ) {
      NameExprPair nameExprPair = (NameExprPair) iter.next();

      DeclName declName = nameExprPair.getName();

      //get the type of the expression
      Expr expr = nameExprPair.getExpr();
      Type exprType = (Type) expr.accept(this);

      //add the name and type to the list
      NameTypePair nameTypePair =
        factory().createNameTypePair(declName, exprType);
      nameTypePairs.add(nameTypePair);
    }

    //create the type
    Signature signature = factory().createSignature(nameTypePairs);
    type = factory().createSchemaType(signature);

    //add the type annotation
    addTypeAnn(bindExpr, type);

    return type;
  }

  //// helper methods /////
  //gets the type of the expression represented by a name
  protected Type getType(Name name)
  {
    //get the type from the TypeEnv
    Type type = typeEnv().getType(name);

    //if the type environment did not know of this expression.
    //then ask the pending env
    if (isUnknownType(type)) {
      type = pending().getType(name);
    }

    //if the pending environment did not know of this expression,
    //then ask the SectTypeEnv
    if (isUnknownType(type)) {
      Type sectTypeEnvType = sectTypeEnv().getType(name);
      if (!isUnknownType(sectTypeEnvType)) {
        type = cloneType(sectTypeEnvType);
      }
    }

    //if not in either environments, or does not start with a
    //delta or xi, return a variable type with the specified name
    if (isUnknownType(type)) {
      DeclName declName =
        factory().createDeclName(name.getWord(), name.getStroke(), null);
      VariableType vType = factory().createVariableType();
      vType.setName(declName);
      type = vType;

      //add an UndeclaredAnn
      UndeclaredAnn ann = new UndeclaredAnn();
      name.getAnns().add(ann);
    }
    else {
      //remove an UndeclaredAnn if there is one
      Object ann = name.getAnn(UndeclaredAnn.class);
      if (ann != null) {
        name.getAnns().remove(ann);
      }
    }

    return type;
  }

  protected boolean signaturesCompatible(Signature left,
                                         Signature right)
  {
    List leftNames = left.getNameTypePair();
    List rightNames = right.getNameTypePair();

    for (Iterator leftIter = leftNames.iterator(); leftIter.hasNext(); ) {
      NameTypePair leftPair = (NameTypePair) leftIter.next();

      for (Iterator rightIter = rightNames.iterator();
           rightIter.hasNext(); ) {
        NameTypePair rightPair = (NameTypePair) rightIter.next();

        //complain if the types to not agree
        if (leftPair.getName().equals(rightPair.getName()) &&
            !unify(unwrapType(leftPair.getType()),
                   unwrapType(rightPair.getType()))) {
          return false;
        }
      }
    }
    return true;
  }

  //decorate each name in a signature with a specified stroke
  protected SchemaType decorate(SchemaType schemaType, List stroke)
  {
    List nameTypePairs = list();

    //add the stroke to each name
    Signature signature = schemaType.getSignature();
    for (Iterator iter = signature.getNameTypePair().iterator();
         iter.hasNext(); ) {
      NameTypePair oldPair = (NameTypePair) iter.next();
      DeclName oldName = oldPair.getName();
      List strokes = list(oldName.getStroke());
      strokes.addAll(stroke);
      DeclName newName =
        factory().createDeclName(oldName.getWord(), strokes, null);
      NameTypePair newPair =
        factory().createNameTypePair(newName, oldPair.getType());
      nameTypePairs.add(newPair);
    }

    Signature newSignature = factory().createSignature(nameTypePairs);
    SchemaType result = factory().createSchemaType(newSignature);

    return result;
  }

  //union two signatures
  protected Signature unionSignatures(Signature leftSig, Signature rightSig)
  {
    //the NameTypePairs to be in the unioned signatures
    List nameTypePairs = list();

    //add all from the left sig
    nameTypePairs.addAll(leftSig.getNameTypePair());

    //for all NameTypePairs in the right signature, only add
    //if they are not in the new signature
    for (Iterator iter = rightSig.getNameTypePair().iterator();
         iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      if (!nameTypePairs.contains(pair)) {
        nameTypePairs.add(pair);
      }
    }

    Signature signature = factory().createSignature(nameTypePairs);
    return signature;
  }

  //subtract the NameTypePairs in rightSig from leftSig
  protected Signature schemaHide(Signature leftSig, Signature rightSig)
  {
    //the list for this signature
    List nameTypePairs = list();

    for (Iterator iter = leftSig.getNameTypePair().iterator();
         iter.hasNext(); ) {
      NameTypePair leftPair = (NameTypePair) iter.next();
      NameTypePair rightPair =
        findInSignature(leftPair.getName(), rightSig);
      if (rightPair == null) {
        nameTypePairs.add(leftPair);
      }
    }

    Signature result = factory().createSignature(nameTypePairs);
    return result;
  }

  //subtract the NameTypePairs from the signature if the name occurs
  //in the list
  protected Signature schemaHide(Signature leftSig, List names)
  {
    //the list of NameTypePairs for this signature
    List nameTypePairs = list();

    for (Iterator iter = leftSig.getNameTypePair().iterator();
         iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();

      //create a RefName with which to search the list of names
      RefName refName =
        factory().createRefName(nameTypePair.getName().getWord(),
                               nameTypePair.getName().getStroke(),
                               null);

      //only add the pair to the new signature if the name is not
      //being hidden
      if (!names.contains(refName)) {
        nameTypePairs.add(nameTypePair);
      }
    }

    //create the new signature
    Signature signature = factory().createSignature(nameTypePairs);
    return signature;
  }

  protected NameTypePair findInSignature(DeclName declName,
                                         Signature signature)
  {
    NameTypePair result = null;
    List pairs = signature.getNameTypePair();
    for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      if (nameTypePair.getName().equals(declName)) {
        result = nameTypePair;
        break;
      }
    }
    return result;
  }

  protected Type instantiate(Type type)
  {
    Type result = unknownType();

    if (isGenericType(type)) {
      Type2 optionalType = (Type2) cloneType(genericType(type).getType());
      if (genericType(type).getOptionalType() != null) {
        optionalType = genericType(type).getOptionalType();
      }
      Type2 instantiated = instantiate(optionalType);
      genericType(type).setOptionalType(instantiated);
      result = type;
    }
    else {
      result = instantiate((Type2) type);
    }

    return result;
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = unknownType();

    if (isGenParamType(type)) {
      GenParamType genParamType = (GenParamType) type;
      DeclName genName = genParamType.getName();

      //try to get the type from the UnificationEnv
      Type unificationEnvType =  unificationEnv().getType(genName);

      //if this type's reference is in the parameters
      if (containsDoubleEquals(typeEnv().getParameters(), genName)) {
        result = type;
      }
      else if (isUnknownType(unificationEnvType) &&
               unknownType(unificationEnvType).getName() == null) {
        VariableType vType = factory().createVariableType();
        result = vType;
        unificationEnv().addGenName(genName, result);
      }
      else if (unificationEnvType instanceof Type2) {
        result = (Type2) unificationEnvType;
      }
      else {
        // TODO: can this happen and what to do now?
        throw new CztException("Cannot instantiate " + type);
      }
    }
    else if (isVariableType(type)) {
      VariableType variableType = (VariableType) type;
      Type unificationEnvType =
        unificationEnv().getType(variableType.getName());
      if (isUnknownType(unificationEnvType) &&
          unknownType(unificationEnvType).getName() == null) {
        result = variableType;
      }
      else if (unificationEnvType instanceof Type2) {
        result = (Type2) unificationEnvType;
      }
      else {
        // TODO: can this happen and what to do now?
        throw new CztException("Cannot instantiate " + type);
      }
    }
    else if (isPowerType(type)) {
      PowerType powerType = (PowerType) type;
      Type2 replaced = instantiate(powerType.getType());
      powerType.setType(replaced);
      result = powerType;
    }
    else if (isGivenType(type)) {
      result = type;
    }
    else if (isSchemaType(type)) {
      SchemaType schemaType = (SchemaType) type;

      List nameTypePairs = schemaType.getSignature().getNameTypePair();
      for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        Type replaced = instantiate(nameTypePair.getType());
        nameTypePair.setType(replaced);
      }

      result = schemaType;
    }
    else if (isProdType(type)) {
      ProdType prodType = (ProdType) type;

      //the list of types for the new instantiated product
      for (int i = 0; i < prodType.getType().size(); i++) {
        Type2 next = (Type2) prodType.getType().get(i);

        Type2 replaced = instantiate(next);
        prodType.getType().set(i, replaced);
      }

      result = prodType;
    }

    return result;
  }
}
