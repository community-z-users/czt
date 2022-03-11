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

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * An <code>ExprChecker</code> instance visits the Exprs instances in
 * an AST, checks them for type consistencies, adding an ErrorAnn
 * if there are inconsistencies.
 *
 * Each visit method to Expr objects return the type (Type2) of the
 * expression.
 */
public class ExprChecker
  extends Checker<Type2>
  implements ExprVisitor<Type2>,
             RefExprVisitor<Type2>,
             PowerExprVisitor<Type2>,
             ProdExprVisitor<Type2>,
             SetExprVisitor<Type2>,
             SetCompExprVisitor<Type2>,
             NumExprVisitor<Type2>,
             SchExprVisitor<Type2>,
             TupleExprVisitor<Type2>,
             TupleSelExprVisitor<Type2>,
             Qnt1ExprVisitor<Type2>,
             LambdaExprVisitor<Type2>,
             MuExprVisitor<Type2>,
             LetExprVisitor<Type2>,
             SchExpr2Visitor<Type2>,
             NegExprVisitor<Type2>,
             CondExprVisitor<Type2>,
             CompExprVisitor<Type2>,
             PipeExprVisitor<Type2>,
             HideExprVisitor<Type2>,
             ProjExprVisitor<Type2>,
             PreExprVisitor<Type2>,
             ApplExprVisitor<Type2>,
             ThetaExprVisitor<Type2>,
             DecorExprVisitor<Type2>,
             RenameExprVisitor<Type2>,
             BindSelExprVisitor<Type2>,
             BindExprVisitor<Type2>
{
  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Type2 visitExpr(Expr expr)
  {
    visitTerm(expr);
    return factory().createVariableType();
  }

  public Type2 visitRefExpr(RefExpr refExpr)
  {
    //get the type of this name
    ZName zName = refExpr.getZName();
    Type type = exprChecker().getType(zName);

    //if the RefExpr referes to a schema, create new IDs for all names
    //in the schema's signature
    SchemaType schType;
    if ((schType = referenceToSchema(type)) != null) {
      Signature signature = schType.getSignature();
      if (! (signature instanceof VariableSignature)) {
        Signature sig = createNewIds(signature);
        SchemaType newSchemaType = factory().createSchemaType(sig);
        type = factory().createPowerType(newSchemaType);
      }
    }

    //add this reference for post checking
    if (!containsObject(paraErrors(), refExpr)) {
      addTermForPostChecking(refExpr);
    }

    //if this is undeclared, create an unknown type with this RefExpr
    Object undecAnn = zName.getAnn(UndeclaredAnn.class);

    //if we are using name IDs, then read the type off the name if it
    //is not in the type environment
    if (undecAnn != null && sectTypeEnv().getUseNameIds()) {
      type = getTypeFromAnns(refExpr);
      if (!(type instanceof UnknownType)) {
        removeAnn(zName, UndeclaredAnn.class);
        undecAnn = null;
      }
    }

    //get an existing parameter annotation
    ParameterAnn pAnn = (ParameterAnn) refExpr.getAnn(ParameterAnn.class);
    List<Expr> exprs = refExpr.getZExprList();

    //if it is a generic type, but has not been declared in the
    //current paragraph, we must instantiate the optional type
    if (type instanceof GenericType && !isPending()) {
      GenericType genericType = (GenericType) type;
      //if the instantiation is implicit
      if (exprs.size() == 0) {
        List<Type2> instantiations = factory().list();
        unificationEnv().enterScope();

        //add new vtypes for the (missing) parameters
        ZNameList genNames = ZUtils.assertZNameList(genericType.getNameList());
        for (Name genName : genNames) {
          //add a variable type corresponding to this name
          VariableType vType = factory().createVariableType();
          unificationEnv().addGenName(genName, vType);
          instantiations.add(vType);
        }

        //instantiate the type
        type = exprChecker().instantiate(genericType);

        if (pAnn != null) {
          removeAnn(refExpr, pAnn);
        }
        pAnn = new ParameterAnn(instantiations);
        addAnn(refExpr, pAnn);
        addAnn(zName, pAnn);
        unificationEnv().exitScope();
      }
      //if the instantiation is explicit
      else {
        ZNameList genNames = ZUtils.assertZNameList(genericType.getNameList());
        if (genNames.size() == exprs.size()) {
          List<Type2> instantiations = factory().list();
          unificationEnv().enterScope();

          //if this has not been visited previously, add the genName
          //and expr pairs into the environment
          for (int i = 0; i < genNames.size(); i++) {
            //get the next name and create a generic types
            Name genName = genNames.get(i);
            Expr expr = exprs.get(i);
            Type2 exprType = expr.accept(exprChecker());
            PowerType vPowerType = factory().createPowerType();
            UResult unified = unify(vPowerType, exprType);

            //if the expr is not a set
            if (unified == FAIL) {
              Object [] params = {expr, exprType};
              error(refExpr, ErrorMessage.NON_SET_IN_INSTANTIATION, params);
            }
            //if the unification succeeds, add this gen name to the
            //unification environment
            else {
              //add the type to the environment
              Type2 substType = vPowerType.getType();
              unificationEnv().addGenName(genName, substType);
              instantiations.add(substType);
            }
          }

          //instantiate the type
          type = exprChecker().instantiate(genericType);

          if (pAnn != null) {
            removeAnn(refExpr, pAnn);
          }
          pAnn = new ParameterAnn(instantiations);
          unificationEnv().exitScope();
        }
        else {
          Object [] params = {refExpr.getZName(), genNames.size()};
          error(refExpr, ErrorMessage.PARAMETER_MISMATCH, params);
        }
      }
    }
    else if (type instanceof GenericType && isPending()) {
      if (exprs.size() > 0) {
        Object [] params = {refExpr.getZName()};
        error(refExpr, ErrorMessage.PARAMETER_MISMATCH_IN_DEFPARA, params);
      }
    }
    else if (undecAnn != null) {
      assert type instanceof UnknownType;
      UnknownType uType = (UnknownType) type;
      uType.setZName(zName);
      for (Expr expr : exprs) {
        Type2 exprType = expr.accept(exprChecker());
        PowerType vPowerType = factory().createPowerType();
        Type2 baseType = factory().createUnknownType();
        UResult unified = unify(vPowerType, exprType);
        if (unified != FAIL) {
          baseType = vPowerType.getType();
        }
        uType.getType().add(baseType);
      }
    }
    else if (!(type instanceof GenericType)) {
      if (exprs.size() > 0) {
        Object [] params = {refExpr.getZName(), 0};
        error(refExpr, ErrorMessage.PARAMETER_MISMATCH, params);
      }
    }

    Type2 result = unwrapType(type);

    //add the type annotation
    addTypeAnn(refExpr, result);

    return result;
  }

  public Type2 visitPowerExpr(PowerExpr powerExpr)
  {
    Type2 type = factory().createUnknownType();

    //get the expr and its type
    Expr expr = powerExpr.getExpr();
    Type2 innerType = expr.accept(exprChecker());

    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, innerType);
    //if the inner expr is not a set, raise an error
    if (unified == FAIL) {
      Object [] params = {powerExpr, innerType};
      error(powerExpr, ErrorMessage.NON_SET_IN_POWEREXPR, params);
    }
    else {
      type = factory().createPowerType(innerType);
    }

    //add the type as an annotation
    addTypeAnn(powerExpr, type);

    return type;
  }

  public Type2 visitProdExpr(ProdExpr prodExpr)
  {
    //the list of types in the expr
    List<Type2> types = factory().list();

    //get and visit the list of expressions
    List<Expr> exprs = prodExpr.getZExprList();
    int position = 1;
    for (Expr expr : exprs) {
      Type2 nestedType = expr.accept(exprChecker());

      PowerType vPowerType = factory().createPowerType();
      UResult unified = unify(vPowerType, nestedType);
      //if the expr is not a set expr, then raise an error
      if (unified == FAIL) {
        Object [] params = {prodExpr, position, nestedType};
        error(prodExpr, ErrorMessage.NON_SET_IN_PRODEXPR, params);
      }
      types.add(vPowerType.getType());
      position++;
    }

    Type2 prodType = factory().createProdType(types);
    PowerType type = factory().createPowerType(prodType);

    //add the type as an annotation
    addTypeAnn(prodExpr, type);

    return type;
  }

  public Type2 visitSetExpr(SetExpr setExpr)
  {
    //get the inner expressions
    List<Expr> exprs = setExpr.getZExprList();

    //first try to get the inner type from the annotation in case this
    //expression has already been visited
    Type2 innerType = null;
    Type2 annType = getType2FromAnns(setExpr);
    if (annType instanceof PowerType) {
      if (!instanceOf(powerType(annType).getType(), UnknownType.class)) {
        innerType = powerType(annType).getType();
      }
    }

    //if the set is not empty find the inner type
    for (Expr expr : exprs) {
      Type2 exprType = expr.accept(exprChecker());

      //if we have no inner type yet, use this exprs type
      if (innerType == null) {
        innerType = exprType;
      }
      else {
        //if the type of this expr does not unify with the previous types,
        //raise an error
        if (unify(innerType, exprType) == FAIL) {
          Object [] params = {setExpr, exprType, innerType};
          error(setExpr, ErrorMessage.TYPE_MISMATCH_IN_SET_EXPR, params);
        }
      }
    }

    //if the set is empty, the inner type is still variable
    if (innerType == null) {
      innerType = factory().createVariableType();
    }

    //if the inner type is not resolved, add this expression to the
    //error list for future evalutation
    if (resolve(innerType) instanceof VariableType &&
        !containsObject(paraErrors(), setExpr)) {
       addTermForPostChecking(setExpr);
    }

    //create the type of this expr
    Type2 type = factory().createPowerType(innerType);

    //add the type as an annotion
    addTypeAnn(setExpr, type);

    return type;
  }

  public Type2 visitNumExpr(NumExpr numExpr)
  {
    //the type of a NumExpr is the given type arithmos
    ZName arithmos = factory().createZName(ZString.ARITHMOS);
    PowerType arithType = (PowerType) sectTypeEnv().getType(arithmos);
    Type2 type = arithType.getType();

    //add the type as an annotation
    addTypeAnn(numExpr, type);

    return type;
  }

  public Type2 visitSchExpr(SchExpr schExpr)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //visit the SchText and add return the signature
    //from that as the signature for this expression
    Signature signature = factory().createSignature();
    SchText schText = schExpr.getSchText();
    if (schText != null) {
      signature = schText.accept(schTextChecker());
    }

    //exit the current scope
    typeEnv().exitScope();

    SchemaType schemaType = factory().createSchemaType(signature);
    PowerType type = factory().createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(schExpr, type);

    return type;
  }

  public Type2 visitSetCompExpr(SetCompExpr setCompExpr)
  {
    //the type of the overall expression
    Type2 type = factory().createUnknownType();

    //enter a new variable scope
    typeEnv().enterScope();

    //get the signature from the SchText
    SchText schText = setCompExpr.getSchText();
    @SuppressWarnings("unused")
	Signature signature = schText.accept(schTextChecker());

    //get the expr
    Expr expr = setCompExpr.getExpr();

    //if the expr is null, then use the schema text to obtain the type
    if (expr == null) {
      //the type is the type of the characteristic tuple of the schema text
      List<Type2> charac = schText.accept(charTupleChecker());
      Type2 innerType = mkTuple(charac);
      type = factory().createPowerType(innerType);
    }
    //if the expr is not null, then the overall type is a power set
    //of the type of expr
    else {
      Type2 exprType = expr.accept(exprChecker());
      type = factory().createPowerType(exprType);
    }

    //exit the variable scope
    typeEnv().exitScope();

    //add the type annotation
    addTypeAnn(setCompExpr, type);

    return type;
  }

  //13.2.6.6
  public Type2 visitTupleExpr(TupleExpr tupleExpr)
  {
    //the individual types of the elements in the tuple
    List<Type2> types = factory().list();

    //get the types of the individual elements
    List<Expr> exprs = tupleExpr.getZExprList();
    for (Expr expr : exprs) {
      Type2 innerType = expr.accept(exprChecker());
      types.add(innerType);
    }

    //create the ProdType from the list of types
    ProdType type = factory().createProdType(types);

    //add the type annotations
    addTypeAnn(tupleExpr, type);

    return type;
  }

  public Type2 visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    //the type of this expression
    Type2 type = factory().createUnknownType();

    //get the types of the expression
    Expr expr = tupleSelExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //if the expression is a ProdType, then find the type
    //of the selection
    Type2 resolved = resolve(exprType);
    if (resolved instanceof ProdType) {
      ProdType prodType = (ProdType) resolved;

      //if the select value is invalid, raise an error
      Numeral numeral = tupleSelExpr.getNumeral();
      int select = ZUtils.assertZNumeral(numeral).getValue().intValue();
      if (select > prodType.getType().size() || select < 1) {
        Object [] params = {tupleSelExpr, prodType.getType().size()};
        error(tupleSelExpr, ErrorMessage.INDEX_ERROR_IN_TUPLESELEXPR, params);
      }
      //otherwise, get the type
      else {
        type = prodType.getType().get(select - 1);
      }
    }
    //if not a ProdType, then raise an error
    else if (!instanceOf(resolved, VariableType.class)) {
      Object [] params = {tupleSelExpr, exprType};
      error(tupleSelExpr, ErrorMessage.NON_PRODTYPE_IN_TUPLESELEXPR, params);
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
  public Type2 visitQnt1Expr(Qnt1Expr qnt1Expr)
  {
    //the type of this expression
    Type2 type = factory().createUnknownType();

    //enter a new variable scope
    typeEnv().enterScope();

    //visit the SchText, but do not add its declarations
    //as global
    SchText schText = qnt1Expr.getSchText();
    Signature signature = schText.accept(schTextChecker());

    //get the type of the expression
    Expr expr = qnt1Expr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //exit a variable scope
    typeEnv().exitScope();

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a schema expr, raise an error
    if (unified == FAIL) {
      Object [] params = {expr, exprType};
      error(expr, ErrorMessage.NON_SCHEXPR_IN_QNT1EXPR, params);
    }
    else {
      //check that the signatures are compatible
      SchemaType schemaType = (SchemaType) vPowerType.getType();
      Signature exprSignature = schemaType.getSignature();
      Signature thisSignature = factory().createVariableSignature();
      if (!instanceOf(exprSignature, VariableSignature.class)) {
        List<NameTypePair> newPairs = factory().list(signature.getNameTypePair());
        newPairs.addAll(exprSignature.getNameTypePair());
        checkForDuplicates(newPairs, qnt1Expr, ErrorMessage.TYPE_MISMATCH_IN_EXPR);

        //if the type of expr is a schema, then assign the type by
        //substracting schText's signature from expr's signature
        thisSignature = schemaHide(schemaType.getSignature(), signature);
      }

      SchemaType thisSchemaType = factory().createSchemaType(thisSignature);
      type = factory().createPowerType(thisSchemaType);
    }

    //add the type annotation
    addTypeAnn(qnt1Expr, type);

    return type;
  }

  public Type2 visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get the signature of the SchText
    SchText schText = lambdaExpr.getSchText();
    schText.accept(schTextChecker());

    List<Type2> charac = schText.accept(charTupleChecker());

    //get the type of the expression
    Expr expr = lambdaExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //exit the variable scope
    typeEnv().exitScope();

    //the characterisitic tuple of the schema text
    Type2 charTuple = mkTuple(charac);

    //the type of this expression is a function from the type of the
    //characteristic tuple to the type of the expression
    ProdType prodType =
      factory().createProdType(factory().list(charTuple, exprType));
    Type2 type = factory().createPowerType(prodType);

    //add the type annotation
    addTypeAnn(lambdaExpr, type);

    return type;
  }

  public Type2 visitMuExpr(MuExpr muExpr)
  {
    Type2 type = factory().createUnknownType();

    //enter a new variable scope
    typeEnv().enterScope();

    //get and visit the SchText
    SchText schText = muExpr.getSchText();
    @SuppressWarnings("unused")
	Signature signature = schText.accept(schTextChecker());

    //get the expr
    Expr expr = muExpr.getExpr();

    //if the expr is not null, calculate the type from the expr
    if (expr != null) {
      type = expr.accept(exprChecker());
    }
    //otherwise, calculate the type from the schema text
    else {
      //the type is the type of the characteristic tuple of the schema text
      List<Type2> charac = schText.accept(charTupleChecker());
      type = mkTuple(charac);
    }

    //exit the current scope
    typeEnv().exitScope();

    //add the type annotation
    addTypeAnn(muExpr, type);

    return type;
  }

  public Type2 visitLetExpr(LetExpr letExpr)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get and visit the SchText
    SchText schText = letExpr.getSchText();
    schText.accept(schTextChecker());

    //calculate the type from the expr
    Expr expr = letExpr.getExpr();
    Type2 type = expr.accept(exprChecker());

    //exit the current scope
    typeEnv().exitScope();

    //add the type annotation
    addTypeAnn(letExpr, type);

    return type;
  }


  /**
   * AndExpr, OrExpr, IffExpr, and ImpliesExpr objects are visited as
   * an instance of their superclass SchExpr2. Other SchExpr2 subclass
   * instances have their own visit method, although ProjExprs use
   * this visit method as well.
   */
  public Type2 visitSchExpr2(SchExpr2 schExpr2)
  {
    //the type of this expression
    Type2 type = factory().createUnknownType();

    //get the types of the left and right expressions
    Expr leftExpr = schExpr2.getLeftExpr();
    Expr rightExpr = schExpr2.getRightExpr();
    Type2 leftType = leftExpr.accept(exprChecker());
    Type2 rightType = rightExpr.accept(exprChecker());

    //get the element types of the expressions
    SchemaType vLeftSchema = factory().createSchemaType();
    PowerType vLeftPower = factory().createPowerType(vLeftSchema);
    SchemaType vRightSchema = factory().createSchemaType();
    PowerType vRightPower = factory().createPowerType(vRightSchema);

    UResult lUnified = unify(vLeftPower, leftType);
    UResult rUnified = unify(vRightPower, rightType);

    //if the left type is not a schema expr, raise an error
    if (lUnified == FAIL) {
      Object [] params = {schExpr2, leftType};
      error(schExpr2, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR2, params);
    }

    //if the right type is not a schema expr, raise an error
    if (rUnified == FAIL) {
      Object [] params = {schExpr2, rightType};
      error(schExpr2, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR2, params);
    }

    //if both types are schema expressions, compute the type
    if (lUnified != FAIL && rUnified != FAIL) {
      Signature leftSig = schemaType(vLeftPower.getType()).getSignature();
      Signature rightSig = schemaType(vRightPower.getType()).getSignature();
      Signature signature = factory().createVariableSignature();
      if (!instanceOf(leftSig, VariableSignature.class) &&
          !instanceOf(rightSig, VariableSignature.class)) {
        List<NameTypePair> newPairs = factory().list(leftSig.getNameTypePair());
        newPairs.addAll(rightSig.getNameTypePair());
        checkForDuplicates(newPairs, schExpr2, ErrorMessage.TYPE_MISMATCH_IN_EXPR);
        signature = factory().createSignature(newPairs);
      }
      SchemaType schemaType = factory().createSchemaType(signature);
      type = factory().createPowerType(schemaType);
    }

    //add the type annotation
    addTypeAnn(schExpr2, type);

    return type;
  }

  public Type2 visitNegExpr(NegExpr negExpr)
  {
    //get the type of the expr, which is the type of the
    //overall expr
    Expr expr = negExpr.getExpr();
    Type2 type = expr.accept(exprChecker());

    //add the type annotation
    addTypeAnn(negExpr, type);

    return type;
  }

  public Type2 visitCondExpr(CondExpr condExpr)
  {
    Type2 type = factory().createVariableType();

    //visit the Pred
    Pred pred = condExpr.getPred();
    UResult solved = pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == PARTIAL) {
      pred.accept(predChecker());
    }

    //get the type of the left and right expr
    Expr leftExpr = condExpr.getLeftExpr();
    Expr rightExpr = condExpr.getRightExpr();
    Type2 leftType = leftExpr.accept(exprChecker());
    Type2 rightType = rightExpr.accept(exprChecker());

    //unify the new type with the left and right types
    UResult lUnified = unificationEnv().unify(leftType, type);
    UResult rUnified = unificationEnv().unify(rightType, type);

    //if the unification failed, raise an error
    if (lUnified == FAIL || rUnified == FAIL) {
      Object [] params = {condExpr, leftType, rightType};
      error(condExpr, ErrorMessage.TYPE_MISMATCH_IN_CONDEXPR, params);
    }

    //add the type annotation
    addTypeAnn(condExpr, type);

    return type;
  }

  public Type2 visitCompExpr(CompExpr compExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr leftExpr = compExpr.getLeftExpr();
    Expr rightExpr = compExpr.getRightExpr();
    Type2 leftType = leftExpr.accept(exprChecker());
    Type2 rightType = rightExpr.accept(exprChecker());

    //get the element types of the expressions
    SchemaType vLeftSchema = factory().createSchemaType();
    PowerType vLeftPower = factory().createPowerType(vLeftSchema);
    SchemaType vRightSchema = factory().createSchemaType();
    PowerType vRightPower = factory().createPowerType(vRightSchema);

    UResult lUnified = unify(vLeftPower, leftType);
    UResult rUnified = unify(vRightPower, rightType);

    //if the left type is not a schema expr, raise an error
    if (lUnified == FAIL) {
      Object [] params = {compExpr, leftType};
      error(compExpr, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR2, params);
    }

    //if the right type is not a schema expr, raise an error
    if (rUnified == FAIL) {
      Object [] params = {compExpr, rightType};
      error(compExpr, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR2, params);
    }

    if (lUnified != FAIL && rUnified != FAIL) {
      SchemaType schemaType = factory().createSchemaType();
      Signature lSig = schemaType(vLeftPower.getType()).getSignature();
      Signature rSig = schemaType(vRightPower.getType()).getSignature();
      if (!instanceOf(lSig, VariableSignature.class) &&
          !instanceOf(rSig, VariableSignature.class)) {
        String errorMessage = ErrorMessage.TYPE_MISMATCH_IN_COMPEXPR.toString();
        Signature signature = createCompSig(lSig, rSig, compExpr, errorMessage);
        checkForDuplicates(signature.getNameTypePair(), 
			   compExpr, 
			   ErrorMessage.TYPE_MISMATCH_IN_EXPR);
        schemaType.setSignature(signature);
      }
      type = factory().createPowerType(schemaType);
    }

    //add the type annotation
    addTypeAnn(compExpr, type);

    return type;
  }

  public Type2 visitPipeExpr(PipeExpr pipeExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr leftExpr = pipeExpr.getLeftExpr();
    Expr rightExpr = pipeExpr.getRightExpr();
    Type2 leftType = leftExpr.accept(exprChecker());
    Type2 rightType = rightExpr.accept(exprChecker());

    //get the element types of the expressions
    SchemaType vLeftSchema = factory().createSchemaType();
    PowerType vLeftPower = factory().createPowerType(vLeftSchema);
    SchemaType vRightSchema = factory().createSchemaType();
    PowerType vRightPower = factory().createPowerType(vRightSchema);

    UResult lUnified = unify(vLeftPower, leftType);
    UResult rUnified = unify(vRightPower, rightType);

    //if the left type is not a schema expr, raise an error
    if (lUnified == FAIL) {
      Object [] params = {pipeExpr, leftType};
      error(pipeExpr, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR2, params);
    }

    //if the right type is not a schema expr, raise an error
    if (rUnified == FAIL) {
      Object [] params = {pipeExpr, rightType};
      error(pipeExpr, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR2, params);
    }

    if (lUnified != FAIL && rUnified != FAIL) {
      SchemaType schemaType = factory().createSchemaType();
      Signature lSig = schemaType(vLeftPower.getType()).getSignature();
      Signature rSig = schemaType(vRightPower.getType()).getSignature();

      if (!instanceOf(lSig, VariableSignature.class) &&
          !instanceOf(rSig, VariableSignature.class)) {
        //create the signature
        String errorMessage = ErrorMessage.TYPE_MISMATCH_IN_PIPEEXPR.toString();
        Signature signature = createPipeSig(lSig, rSig, pipeExpr, errorMessage);
        checkForDuplicates(signature.getNameTypePair(), 
			   pipeExpr,
			   ErrorMessage.TYPE_MISMATCH_IN_EXPR);
        schemaType.setSignature(signature);
      }
      type = factory().createPowerType(schemaType);
    }

    //add the type annotation
    addTypeAnn(pipeExpr, type);
    return type;
  }

  //C.6.16
  public Type2 visitHideExpr(HideExpr hideExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr expr = hideExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a schema expr, raise an error
    if (unified == FAIL) {
      Object [] params = {hideExpr, exprType};
      error(hideExpr, ErrorMessage.NON_SCHEXPR_IN_HIDE_EXPR, params);
    }
    //if the expr is a schema expr, hide the names in the list
    else {
      //hide the declarations
      SchemaType schemaType = (SchemaType) vPowerType.getType();
      Signature signature = schemaType.getSignature();
      SchemaType hideSchemaType = factory().createSchemaType();
      if (!instanceOf(signature, VariableSignature.class)) {
        Signature hideSig =
          createHideSig(signature, hideExpr.getZNameList(), hideExpr);
        checkForDuplicates(hideSig.getNameTypePair(), 
			   hideExpr, 
			   ErrorMessage.TYPE_MISMATCH_IN_EXPR);
        hideSchemaType.setSignature(hideSig);
      }
      type = factory().createPowerType(hideSchemaType);
    }

    //add the type annotation
    addTypeAnn(hideExpr, type);

    return type;
  }

  //C.6.17
  public Type2 visitProjExpr(ProjExpr projExpr)
  {
    //visit this type as a SchExpr2
    visitSchExpr2(projExpr);

    //the type of this expression is the same as the right expr
    Type2 type = getType2FromAnns(projExpr.getRightExpr());

    //add the type annotation
    addTypeAnn(projExpr, type);

    return type;
  }

  //C.6.18
  public Type2 visitPreExpr(PreExpr preExpr)
  {
    //the type of this expression
    Type2 type = factory().createUnknownType();

    //visit the expr
    Expr expr = preExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a schema expr, raise an error
    if (unified == FAIL) {
      Object [] params = {preExpr, exprType};
      error(preExpr, ErrorMessage.NON_SCHEXPR_IN_PREEXPR, params);
    }
    //the type of the expression is the same a preExpr, with all
    //primed and shrieked variables hidden
    else {
      SchemaType preSchemaType = schemaType(vPowerType.getType());
      Signature preSignature = preSchemaType.getSignature();
      SchemaType schemaType = factory().createSchemaType();
      if (!instanceOf(preSignature, VariableSignature.class)) {
        List<NameTypePair> oldPairs =
          preSchemaType.getSignature().getNameTypePair();
        NextStroke nextStroke = factory().createNextStroke();
        OutStroke outStroke = factory().createOutStroke();

        //the list of NameTypePairs for the new signature
        List<NameTypePair> newPairs = factory().list();
        for (NameTypePair oldPair : oldPairs) {
          //the strokes of this name
          ZStrokeList strokes = oldPair.getZName().getZStrokeList();

          //if the last stroke is not a prime or shriek, then add
          //to the new signature
          int size = strokes.size();
          if (size == 0 ||
              (size > 0 &&
               !(strokes.get(size - 1).equals(nextStroke) ||
                 strokes.get(size - 1).equals(outStroke)))) {
            newPairs.add(oldPair);
          }
        }
        //create the new signature from the new list of pairs
        Signature signature = factory().createSignature(newPairs);
        schemaType.setSignature(signature);
      }
      //create the type
      type = factory().createPowerType(schemaType);
    }

    //add the type annotation
    addTypeAnn(preExpr, type);

    return type;
  }

  //C.6.21
  public Type2 visitApplExpr(ApplExpr applExpr)
  {
    //the type of this expression
    Type2 type = factory().createUnknownType();

    //get the type of the left and right expressions
    Expr funcExpr = applExpr.getLeftExpr();
    Expr argExpr = applExpr.getRightExpr();
    Type2 funcType = funcExpr.accept(exprChecker());
    Type2 argType = argExpr.accept(exprChecker());

    Type2 domType = factory().createVariableType();
    Type2 ranType = factory().createVariableType();
    List<Type2> types = factory().<Type2>list(domType, ranType);
    ProdType vProdType = factory().createProdType(types);
    PowerType vPowerType = factory().createPowerType(vProdType);

    //infer the types of the domain and range. strongUnify is used
    //because we can infer the minimal type from this one inference
    //even if they are class types.
    UResult unified = strongUnify(vPowerType, funcType);

    //if the left expression is not a function, raise an error
    if (unified == FAIL) {
      Object [] params = {applExpr, funcType};
      error(applExpr, ErrorMessage.NON_FUNCTION_IN_APPLEXPR, params);
    }
    else {
      //the type of the domain of the function must unify with the
      //type of the argument
      unified = unify(resolve(domType), argType);
      if (unified == FAIL) {
        Object [] params = {applExpr, resolve(domType), argType};
        error(applExpr, ErrorMessage.TYPE_MISMATCH_IN_APPLEXPR, params);
      }
      else {
        //if the domain and argument unify, then the type is the range type
        type = resolve(ranType);
      }
    }

    //add the type annotation
    addTypeAnn(applExpr, type);
    return type;
  }

  public Type2 visitThetaExpr(ThetaExpr thetaExpr)
  {
    Type2 type = factory().createUnknownType();

    //visit the expr
    Expr expr = thetaExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a schema type, raise an error
    if (unified == FAIL) {
      Object [] params = {thetaExpr, exprType};
      error(thetaExpr, ErrorMessage.NON_SCHEXPR_IN_THETAEXPR, params);
    }
    //otherwise, the type of the whole expression is the base type of
    //the expr
    else {
      SchemaType schemaType = (SchemaType) vPowerType.getType();
      Signature signature = schemaType.getSignature();
      if (!instanceOf(signature, VariableSignature.class)) {
        //check that each name in the signature is present in the
        //environment, which any decorations
        List<NameTypePair> pairs = signature.getNameTypePair();
        for (NameTypePair pair : pairs) {
          //add the strokes to the name
          ZName name = factory().createZName(pair.getZName(), false);
          name.getZStrokeList().addAll(thetaExpr.getZStrokeList());

          //lookup the name in the environment
          Type envType = getType(name);
          Object undecAnn = name.getAnn(UndeclaredAnn.class);
          //if the name is undeclared, copy the annotation to the name
          //in the signature
          if (undecAnn != null) {
            pair.getZName().getAnns().add(undecAnn);
            if (!containsObject(paraErrors(), thetaExpr)) {
              addTermForPostChecking(thetaExpr);
            }
          }

          //if the type of the name is generic, raise an error
          if (envType instanceof GenericType) {
            Object [] params = {name, thetaExpr, exprType};
            error(thetaExpr, ErrorMessage.GENERICTYPE_IN_THETAEXPR, params);
          }
          else {
            //if the type in the signature and the type in the
            //environment are not the same, raise an error
            Type2 envType2 = (Type2) envType;
            Type2 pairType2 = unwrapType(pair.getType());

            unified = unify(envType2, pairType2);
            if (unified == FAIL) {
              Object [] params = {name, thetaExpr, envType2, pairType2};
              error(thetaExpr, ErrorMessage.TYPE_MISMATCH_IN_THETAEXPR, params);
            }
          }
        }
      }
      type = vPowerType.getType();
    }

    //add the type annotation
    addTypeAnn(thetaExpr, type);

    return type;
  }

  public Type2 visitDecorExpr(DecorExpr decorExpr)
  {
    Type2 type = factory().createUnknownType();

    //visit the expr
    Expr expr = decorExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a schema type, raise an error
    if (unified == FAIL) {
      Object [] params = {decorExpr, exprType};
      error(decorExpr, ErrorMessage.NON_SCHEXPR_IN_DECOREXPR, params);
    }
    //if the expr is a schema reference, decorate each name in the
    //signature
    else {
      SchemaType schemaType = (SchemaType) vPowerType.getType();
      Signature signature = schemaType.getSignature();
      SchemaType decorSchemaType = factory().createSchemaType();
      if (!instanceOf(signature, VariableSignature.class)) {
        ZStrokeList strokes = factory().getZFactory().createZStrokeList();
        strokes.add(decorExpr.getStroke());
        decorSchemaType = decorate(schemaType, strokes);
      }
      type = factory().createPowerType(decorSchemaType);
    }

    //add the type annotation
    addTypeAnn(decorExpr, type);

    return type;
  }

  public Type2 visitRenameExpr(RenameExpr renameExpr)
  {
    Type2 type = factory().createUnknownType();

    //visit the expr
    Expr expr = renameExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a schema type, raise an error
    if (unified == FAIL) {
      Object [] params = {renameExpr, exprType};
      error(renameExpr, ErrorMessage.NON_SCHEXPR_IN_RENAMEEXPR, params);
    }
    //if the expr is a schema reference, perform the renaming
    else {
      //add declname IDs to the new names
      addNameIDs(renameExpr);

      //rename the signature
      SchemaType schemaType = schemaType(vPowerType.getType());
      Signature signature = schemaType.getSignature();
      SchemaType newSchemaType = factory().createSchemaType();
      if (!instanceOf(signature, VariableSignature.class)) {
        String errorMessage =
          ErrorMessage.DUPLICATE_NAME_IN_RENAMEEXPR.toString();
        List<NewOldPair> renamePairs = renameExpr.getZRenameList();
        Signature newSig = createRenameSig(signature, renamePairs,
                                           renameExpr, errorMessage);
        checkForDuplicates(newSig.getNameTypePair(), 
			   renameExpr, 
			   ErrorMessage.TYPE_MISMATCH_IN_EXPR);
        newSchemaType.setSignature(newSig);
      }
      type = factory().createPowerType(newSchemaType);
    }

    //add the type annotation
    addTypeAnn(renameExpr, type);

    return type;
  }

  public Type2 visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    Type2 type = factory().createUnknownType();

    //get the type of the expression
    Expr expr = bindSelExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    SchemaType vSchemaType = factory().createSchemaType();

    //if the expr is not a binding, raise an error
    UResult unified = unify(vSchemaType, exprType);
    if (unified == FAIL) {
      Object [] params = {bindSelExpr, exprType};
      error(bindSelExpr, ErrorMessage.NON_BINDING_IN_BINDSELEXPR, params);
    }
    //if expr is a binding, then get the type of the name
    else {
      ZName selectName = bindSelExpr.getZName();
      Signature signature = vSchemaType.getSignature();
      if (!instanceOf(signature, VariableSignature.class)) {
        //if the select name is not in the signature, raise an error
        NameTypePair pair = findNameTypePair(selectName, signature);
        if (pair == null) {
          Object [] params = {bindSelExpr};
          error(selectName, ErrorMessage.NON_EXISTENT_SELECTION, params);
        }
        //otherwise, get the type of that pair
        else {
          type = unwrapType(pair.getType());
        }
      }
    }

    //try to resolve this type if it is unknown
    type = resolveUnknownType(type);

    //add the annotation
    addTypeAnn(bindSelExpr, type);
    return type;
  }

  public Type2 visitBindExpr(BindExpr bindExpr)
  {
    //a list for checking duplicate names
    List<ZName> names = factory().list();

    //the list for create the signature
    List<NameTypePair> pairs = factory().list();

    DeclList declList = bindExpr.getDeclList();
    List<NameTypePair> decls = declList.accept(declChecker());
    for (NameTypePair decl : decls) {
      ZName zName = decl.getZName();
      //if this name is duplicated, raise an error
      if (ZUtils.containsZName(names, zName)) {
        Object [] params = {bindExpr, zName};
        error(bindExpr, ErrorMessage.DUPLICATE_IN_BINDEXPR, params);
      }
      else {
        //get the type of the expression
        Type2 exprType = (Type2) decl.getType();
        //add the name and type to the list
        NameTypePair pair = factory().createNameTypePair(zName, exprType);
        pairs.add(pair);
        names.add(zName);
      }
    }

    //create the type
    Signature signature = factory().createSignature(pairs);
    SchemaType type = factory().createSchemaType(signature);

    //add the type annotation
    addTypeAnn(bindExpr, type);

    return type;
  }

  //// helper methods /////
  //decorate each name in a signature with a specified stroke
  protected SchemaType decorate(SchemaType schemaType, ZStrokeList stroke)
  {
    List<NameTypePair> nameTypePairs = factory().list();

    //add the stroke to each name
    List<NameTypePair> pairs = schemaType.getSignature().getNameTypePair();
    for (NameTypePair oldPair : pairs) {
      ZName oldName = oldPair.getZName();
      ZStrokeList strokes = factory().getZFactory().createZStrokeList();
      strokes.addAll(oldName.getZStrokeList());
      strokes.addAll(stroke);
      ZName newName = factory().createZDeclName(oldName.getWord(), strokes);
      copyLocAnn(oldName, newName);
      NameTypePair newPair =
        factory().createNameTypePair(newName, oldPair.getType());
      nameTypePairs.add(newPair);
    }

    Signature newSignature = factory().createSignature(nameTypePairs);
    SchemaType result = factory().createSchemaType(newSignature);

    return result;
  }

  //subtract the NameTypePairs in rSig from lSig
  protected Signature schemaHide(Signature lSig, Signature rSig)
  {
    //the list for this signature
    List<NameTypePair> pairs = factory().list();
    List<NameTypePair> lPairs = lSig.getNameTypePair();
    for (NameTypePair lPair : lPairs) {
      NameTypePair rPair = findNameTypePair(lPair.getZName(), rSig);
      if (rPair == null) {
        pairs.add(lPair);
      }
    }
    Signature result = factory().createSignature(pairs);
    return result;
  }

  //subtract the NameTypePairs from the signature if the name occurs
  //in the list
  protected Signature schemaHide(Signature lSig, List<ZName> names)
  {
    //the list of NameTypePairs for this signature
    List<NameTypePair> pairs = factory().list();
    List<NameTypePair> oldPairs = lSig.getNameTypePair();
    for (NameTypePair pair : oldPairs) {
      //create a ZName with which to search the list of names
      ZName zName = factory().createZName(pair.getZName(), false);

      //only add the pair to the new signature if the name is not
      //being hidden
      if (!names.contains(zName)) {
        pairs.add(pair);
      }
    }

    //create the new signature
    Signature signature = factory().createSignature(pairs);
    return signature;
  }
}
