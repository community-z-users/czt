package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.io.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * Typechecks an annotated Z AST.
 */
public class TypeChecker
  implements SpecVisitor,
             ZSectVisitor,
             //ParentVisitor,
             GivenParaVisitor,
             AxParaVisitor,
             FreeParaVisitor,
             FreetypeVisitor,
             ConjParaVisitor,
             SchTextVisitor,
             VarDeclVisitor,
             ConstDeclVisitor,
             InclDeclVisitor,
             RefExprVisitor,
             PowerExprVisitor,
             ProdExprVisitor,
             SetExprVisitor,
             SetCompExprVisitor,
             //NumExprVisitor,
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
             //CompExprVisitor,
             //PipeExprVisitor,
             //HideExprVisitor,
             //ProjExprVisitor,
             //PreExprVisitor,
             ApplExprVisitor,
             ThetaExprVisitor,
             //DecorExprVisitor,
             //RenameExprVisitor,
             BindSelExprVisitor,
             BindExprVisitor,
             QntPredVisitor,
             Pred2Visitor,
             AndPredVisitor,
             MemPredVisitor,
             NegPredVisitor,
             ExprPredVisitor
{
  //whether the print debugging info
  protected static final boolean DEBUG = false;

  //A ZFactory
  protected ZFactory factory_;

  //the environment recording a name, its type, and the section in
  //which it was declared
  protected SectTypeEnv sectTypeEnv_;

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv_;

  //the list of errors thrown by retrieving type info
  protected List errors_;

  //the factory for creating error messages
  protected ErrorFactory errorFactory_;

  //for storing the name of the current section
  protected String sectName_;

  protected SectionManager manager_;

  public TypeChecker(SectionManager manager, ErrorFactory errorFactory)
  {
    manager_ = manager;
    errorFactory_ = errorFactory;
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    sectName_ = null;
    sectTypeEnv_ = null;
    errors_ = list();
    unificationEnv_ = new UnificationEnv();
  }

  public TypeChecker(SectionManager manager)
  {
    this(manager, new DefaultErrorFactory(manager));
  }

  public Object visitSpec(Spec spec)
  {
    //the list of section names
    List names = list();

    //visit each section of the specification
    List sects = spec.getSect();
    for (Iterator iter = sects.iterator(); iter.hasNext(); ) {
      Sect sect = (Sect) iter.next();

      //if this is a Z section, check that the name is not
      //already declared in this specification
      if (sect instanceof ZSect) {
        ZSect zSect = (ZSect) sect;
        if (names.contains(zSect.getName())) {
          ErrorAnn message = errorFactory_.redeclaredSection(zSect);
          error(zSect, message);
        }
        else {
          names.add(zSect.getName());
        }
      }

      sect.accept(this);
    }

    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    //the list of section names
    List names = list();

    debug("ZSect name is: " + zSect.getName());
    sectName_ = zSect.getName();

    //get and visit the parent sections of the current section
    List parents = zSect.getParent();
    for (Iterator iter = parents.iterator(); iter.hasNext(); ) {
      Parent parent = (Parent) iter.next();

      if (names.contains(parent.getWord())) {
        ErrorAnn message = errorFactory_.redeclaredParent(parent, sectName_);
        error(parent, message);
      }
      else if (parent.getWord().equals(sectName_)) {
        ErrorAnn message = errorFactory_.selfParent(parent);
        error(parent, message);
      }
      else {
        names.add(parent.getWord());
      }

      parent.accept(this);
    }

    //get and visit the paragraphs of the current section
    List paras = zSect.getPara();
    for (Iterator iter = paras.iterator(); iter.hasNext(); ) {
      Para para = (Para) iter.next();
      para.accept(this);
    }

    //print any errors
    for (Iterator iter = errors_.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      System.err.println(next.toString());
    }
    return null;
  }

  public Object visitGivenPara(GivenPara givenPara)
  {
    debug("visiting GivenPara!!!");

    List names = list();

    //check for duplicates and strokes in the names
    List declNames = givenPara.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      if (declName.getStroke().size() > 0) {
        ErrorAnn message = errorFactory_.strokeInGiven(declName);
        error(declName, message);
      }
      else if (names.contains(declName.getWord())) {
        ErrorAnn message = errorFactory_.redeclaredGiven(declName);
        error(declName, message);
      }
      else {
        names.add(declName.getWord());
      }
    }

    return null;
  }

  public Object visitAxPara(AxPara axPara)
  {
    debug("visiting AxPara");

    List names = list();

    //check for duplicates and strokes in the parameters
    List declNames = axPara.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      if (declName.getStroke().size() > 0) {
        ErrorAnn message = errorFactory_.strokeInGen(declName);
        error(declName, message);
      }
      else if (names.contains(declName.getWord())) {
        ErrorAnn message = errorFactory_.redeclaredGen(declName);
        error(declName, message);
      }
      else {
        names.add(declName.getWord());
      }
    }

    //typechecker the schema text
    SchText schText = axPara.getSchText();
    schText.accept(this);

    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    //visit each Freetype
    List freetypes = freePara.getFreetype();
    for (Iterator iter = freetypes.iterator(); iter.hasNext(); ) {
      Freetype freetype = (Freetype) iter.next();
      freetype.accept(this);
    }

    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    //visit each Branch
    List branchs = freetype.getBranch();
    for (Iterator iter = branchs.iterator(); iter.hasNext(); ) {
      Branch branch = (Branch) iter.next();
      branch.accept(this);
    }
    return null;
  }

  public Object visitBranch(Branch branch)
  {
    Expr expr = branch.getExpr();
    if (expr != null) {
      expr.accept(this);
    }

    //if this branch is an injection, then the expr must be a set
    if (expr != null) {
      Type type = getTypeFromAnns(expr);

      if (isUnknownType(type)) {
        ErrorAnn message = errorFactory_.unknownType(expr);
        error(expr, message);
      }
      else if (!isPowerType(type)) {
        ErrorAnn message = errorFactory_.nonSetInFreeType(expr, type);
        error(expr, message);
      }
    }

    return null;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    List names = list();

    //check for duplicates and strokes in the parameters
    List declNames = conjPara.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      if (declName.getStroke().size() > 0) {
        ErrorAnn message = errorFactory_.strokeInGen(declName);
        error(declName, message);
      }
      else if (names.contains(declName.getWord())) {
        ErrorAnn message = errorFactory_.redeclaredGen(declName);
        error(declName, message);
      }
      else {
        names.add(declName.getWord());
      }
    }

    //visit the predicate
    Pred pred = conjPara.getPred();
    pred.accept(this);

    return null;
  }

  public Object visitSchText(SchText schText)
  {
    //get and visit the list of declarations
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      decl.accept(this);
    }

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      pred.accept(this);
    }

    return null;
  }


  // 13.2.6.13
  public Object visitVarDecl(VarDecl varDecl)
  {
    //visit the expression
    Expr expr = varDecl.getExpr();
    expr.accept(this);

    //check that the expr is a set
    Type type = getTypeFromAnns(expr);
    if (isUnknownType(type)) {
      ErrorAnn message = errorFactory_.unknownType(expr);
      error(expr, message);
    }
    else if (!isPowerType(type)) {
      ErrorAnn message = errorFactory_.nonSetInDecl(expr, type);
      error(expr, message);
    }

    return null;
  }


  public Object visitConstDecl(ConstDecl constDecl)
  {
    //get and visit the expression
    Expr expr = constDecl.getExpr();
    expr.accept(this);

    return null;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    //get and visit the expression
    Expr expr = inclDecl.getExpr();
    expr.accept(this);

    Type exprType = getTypeFromAnns(expr);
    if (!isSchemaType(exprType)) {
      ErrorAnn message = errorFactory_.nonSchExprInInclDecl(inclDecl);
      error(inclDecl, message);
    }

    return null;
  }

  /////// expressions ///////
  public Object visitRefExpr(RefExpr refExpr)
  {
    //visit each expr
    List exprs = refExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type exprType = getTypeFromAnns(expr);

      //check that the type is a set
      if (!isPowerType(exprType)) {
        ErrorAnn message =
          errorFactory_.nonSetInInstantiation(expr, exprType);
      }
      else {
        expr.accept(this);
      }
    }

    return null;
  }

  // 13.2.6.5
  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    Expr expr = powerExpr.getExpr();
    expr.accept(this);

    Type type = getTypeFromAnns(expr);
    if (isUnknownType(type)) {
      ErrorAnn message = errorFactory_.unknownType(expr);
      error(expr, message);
    }
    else if (!isPowerType(type)) {
      ErrorAnn message = errorFactory_.nonSetInPowerExpr(powerExpr, type);
      error(powerExpr, message);
    }

    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    Type baseType = null;

    //check that all elements have the same time
    List exprs = setExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type exprType = getTypeFromAnns(expr);

      if (baseType == null) {
        baseType = exprType;
      }
      else {
        //if the base type is not the same as the next expression
        if (!exprType.equals(baseType)) {
          ErrorAnn message =
            errorFactory_.typeMismatchInSetExpr(expr, exprType, baseType);
          error(setExpr, message);
          break;
        }
      }

      //visit the expression
      expr.accept(this);
    }

    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    //get and visit the list of expressions
    List exprs = prodExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      expr.accept(this);
    }

    return null;
  }

  // 13.2.6.14
  public Object visitSchExpr(SchExpr schExpr)
  {
    //visit the schema text
    SchText schText = schExpr.getSchText();
    schText.accept(this);

    return null;
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    //visit the schema text
    SchText schText = setCompExpr.getSchText();
    schText.accept(this);

    //visit the expr
    Expr expr = setCompExpr.getExpr();
    if (expr != null) {
      expr.accept(this);
    }

    return null;
  }

  // 13.2.6.6
  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    //visit each expression
    List exprs = tupleExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      expr.accept(this);
    }

    return null;
  }

  // 13.2.6.7
  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    Expr expr = tupleSelExpr.getExpr();
    expr.accept(this);

    Type exprType = getTypeFromAnns(expr);

    //report an error if the type of the expression is unknown
    if (isUnknownType(exprType)) {
      ErrorAnn message = errorFactory_.unknownType(expr);
      error(expr, message);
    }
    //if the type is not a cross product, report an error
    else if (!isProdType(exprType)) {
      ErrorAnn message =
        errorFactory_.nonProdTypeInTupleSelExpr(tupleSelExpr, exprType);
      error(tupleSelExpr, message);
    }
    else {
      //if the selection index is less than 1, or greater than the
      //the tuple length, report an error
      ProdType prodType = prodType(exprType);
      if (tupleSelExpr.getSelect().intValue() > prodType.getType().size() ||
          tupleSelExpr.getSelect().intValue() < 1) {

        ErrorAnn message =
          errorFactory_.indexErrorInTupleSelExpr(tupleSelExpr, prodType);
        error(tupleSelExpr, message);
      }
    }

    return null;
  }

  /**
   * ExistsExpr, ExistsExpr, and ForallExpr instances are
   * visited as an instance of their super class Qnt1Expr.
   * Other Qnt1Expr instances are visited by their own visit
   * methods
   */
  public Object visitQnt1Expr(Qnt1Expr qnt1Expr)
  {
    SchText schText = qnt1Expr.getSchText();
    schText.accept(this);

    Expr expr = qnt1Expr.getExpr();
    expr.accept(this);

    Type type = getTypeFromAnns(expr);

    //if the expr is not a schema reference, produce an error
    if (!isPowerType(type) ||
        !isSchemaType(powerType(type).getType())) {
      ErrorAnn message =
        errorFactory_.nonSchExprInQnt1Expr(qnt1Expr, type);
      error(expr, message);
    }
    else {
      SchemaType schemaType = schemaType(powerType(type).getType());

      //if the expr is a schema type, check that all the names being used
      //are declared
      /** TO DO **/
    }

    return null;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    //visit the schema text
    SchText schText = lambdaExpr.getSchText();
    schText.accept(this);

    //visit the expr
    Expr expr = lambdaExpr.getExpr();
    expr.accept(this);

    return null;
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
     //visit the schema text
    SchText schText = muExpr.getSchText();
    schText.accept(this);

    //visit the expr
    Expr expr = muExpr.getExpr();
    if (expr != null) {
      expr.accept(this);
    }

    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
     //visit the schema text
    SchText schText = letExpr.getSchText();
    schText.accept(this);

    //visit the expr
    Expr expr = letExpr.getExpr();
    expr.accept(this);

    return null;
  }

  /**
   * AndExpr, OrExpr, IffExpr, and ImpliesExpr objects are visited as
   * an instance of their superclass SchExpr2. Other SchExpr2 subclass
   * instances have their own visit method
   */
  public Object visitSchExpr2(SchExpr2 schExpr2)
  {
    //the type of this expression
    Type type = UnknownTypeImpl.create();

    //get the types of the left and right expressions
    Expr leftExpr = schExpr2.getLeftExpr();
    Expr rightExpr = schExpr2.getRightExpr();
    leftExpr.accept(this);
    rightExpr.accept(this);

    return null;
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    //visit the expr
    Expr expr = negExpr.getExpr();
    expr.accept(this);

    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    //visit the Pred
    Pred pred = condExpr.getPred();
    pred.accept(this);

    //typecheck the left and right expr
    Expr leftExpr = condExpr.getLeftExpr();
    Expr rightExpr = condExpr.getRightExpr();
    leftExpr.accept(this);
    rightExpr.accept(this);

    //get the type of the left and right expr
    Type leftExprType = getTypeFromAnns(leftExpr);
    Type rightExprType = getTypeFromAnns(rightExpr);

    //if the two expression have different types, complain
    if (!typesEqual(leftExprType, rightExprType)) {
      ErrorAnn message =
        errorFactory_.typeMismatchInCondExpr(condExpr,
                                             leftExprType,
                                             rightExprType);
      error(condExpr, message);
    }

    return null;
  }

  // 13.2.6.8
  public Object visitBindExpr(BindExpr bindExpr)
  {
    List names = list();

    //check for duplicate names
    for (Iterator iter = bindExpr.getNameExprPair().iterator();
         iter.hasNext(); ) {
      NameExprPair nameExprPair = (NameExprPair) iter.next();

      if (names.contains(nameExprPair.getName())) {
        ErrorAnn message =
          errorFactory_.duplicateInBindExpr(bindExpr, nameExprPair.getName());
        error(bindExpr, message);
      }
      else {
        names.add(nameExprPair.getName());
      }

      //visit the expression
      nameExprPair.getExpr().accept(this);
    }

    return null;
  }

  // 13.2.6.9
  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    //typecheck the expression
    Expr expr = thetaExpr.getExpr();
    expr.accept(this);

    //check that the expression is a schema expr
    Type exprType = getTypeFromAnns(expr);
    Type baseType = getBaseType(exprType);
    if (!isSchemaType(baseType)) {
      ErrorAnn message =
        errorFactory_.nonSchExprInThetaExpr(thetaExpr, exprType);
      error(expr, message);
    }

    return null;
  }

  // 13.2.6.10
  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    //typecheck the expression
    Expr expr = bindSelExpr.getExpr();
    expr.accept(this);

    //check that the type of the expr is a schema type
    Type exprType = getTypeFromAnns(expr);
    if (!isSchemaType(exprType)) {
      ErrorAnn message =
        errorFactory_.nonSchTypeInBindSelExpr(bindSelExpr, exprType);
      error(bindSelExpr, message);
    }
    else {
      //check that the selection is a valid name
      SchemaType schemaType = (SchemaType) exprType;
      RefName refName = bindSelExpr.getName();
      boolean found = false;
      for (Iterator iter =
             schemaType.getSignature().getNameTypePair().iterator();
           iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        if (refName.getWord().equals(nameTypePair.getName().getWord()) &&
            refName.getStroke().equals(nameTypePair.getName().getStroke())) {
          found = true;
        }
      }

      if (!found) {
        ErrorAnn message =
          errorFactory_.nonExistentSelection(bindSelExpr, refName);
        error(refName, message);
      }
    }

    return null;
  }

  // 13.2.6.11
  public Object visitApplExpr(ApplExpr applExpr)
  {
    //visit the left and right expressions
    Expr leftExpr = applExpr.getLeftExpr();
    Expr rightExpr = applExpr.getRightExpr();
    leftExpr.accept(this);
    rightExpr.accept(this);

    //get the types
    Type leftType = getTypeFromAnns(leftExpr);
    Type rightType = getTypeFromAnns(rightExpr);

    Type leftBaseType = getBaseType(leftType);

    //if the left expression is a power set of a cross product, then
    //the type of the second component is the type of the whole
    //expression
    if (!isProdType(leftBaseType) ||
        prodType(leftBaseType).getType().size() != 2) {
      ErrorAnn message =
        errorFactory_.nonFunctionInApplExpr(applExpr, leftType);
      error(applExpr, message);
    }
    else {
      ProdType leftProdType = (ProdType) leftBaseType;
      Type firstType = (Type) leftProdType.getType().get(0);

      unificationEnv_.enterScope();
      if (!typesUnify(firstType, rightType)) {
        ErrorAnn message =
          errorFactory_.typeMismatchInApplExpr(applExpr, firstType, rightType);
        error(applExpr, message);
      }
      unificationEnv_.exitScope();
    }

    return null;
  }

  ///// predicates /////////

  /**
   * Exists1Pred, ExistsPred, and ForallPred instances are
   * visited as an instance of their super class QntPred.
   */
  public Object visitQntPred(QntPred qntPred)
  {
    SchText schText = qntPred.getSchText();
    schText.accept(this);

    //visit the Pred
    Pred pred = qntPred.getPred();
    pred.accept(this);

    return null;
  }

  /**
   * IffPred, ImpliesPred, and OrPred instances  are
   * visited as an instance of their super class Pred2.
   */
  public Object visitPred2(Pred2 pred2)
  {
    //visit the left and right preds
    Pred leftPred = pred2.getLeftPred();
    leftPred.accept(this);

    Pred rightPred = pred2.getRightPred();
    rightPred.accept(this);

    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    //first, visit it as a Pred2
    visitPred2(andPred);

    //if the conjunction is a chain (e.g. a=b=c), then we must check
    //that the overlapping expressions are compatible
    if (Op.Chain.equals(andPred.getOp())) {
    }

    return null;
  }

  public Object visitMemPred(MemPred memPred)
  {
    //visit the left and right expressions
    Expr leftExpr = memPred.getLeftExpr();
    leftExpr.accept(this);

    Expr rightExpr = memPred.getRightExpr();
    rightExpr.accept(this);

    //the base of the RHS must unify with the LHS's type
    Type leftType = getTypeFromAnns(leftExpr);
    Type rightType = getTypeFromAnns(rightExpr);
    Type rightBaseType = getBaseType(rightType);

    //if this pred is an equality
    boolean mixfix = memPred.getMixfix().booleanValue();
    if (mixfix && rightExpr instanceof SetExpr) {

      if (!typesEqual(leftType, rightBaseType)) {
        ErrorAnn message =
          errorFactory_.typeMismatchInEquality(memPred,
                                               leftType,
                                               rightBaseType);
        error(memPred, message);
      }
    }
    //if this is a membership
    else if (!mixfix) {
      if (!typesEqual(leftType, rightBaseType)) {
        ErrorAnn message =
          errorFactory_.typeMismatchInMemPred(memPred, leftType, rightType);
        error(memPred, message);
      }
    }
    //if it a relation other than equals or membership
    else {
      unificationEnv_.enterScope();
      if (!typesUnify(rightBaseType, leftType)) {
        ErrorAnn message =
          errorFactory_.typeMismatchInRelOp(memPred, leftType, rightBaseType);
        error(memPred, message);
      }
      unificationEnv_.exitScope();
    }

    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    //visit the predicate
    Pred pred = negPred.getPred();
    pred.accept(this);

    return null;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    //visit the expression
    Expr expr = exprPred.getExpr();
    expr.accept(this);

    return null;
  }

  //------------------------ visit methods stop here-----------------------//
  //-----------------------------------------------------------------------//

  //replace all references to generic types by their actual counterparts
  protected boolean typesUnify(Type formal, Type actual)
  {
    boolean result = true;

    if (isGenParamType(formal)) {
      GenParamType formalGen = (GenParamType) formal;
      result = unificationEnv_.add(formalGen.getName(), (Type2) actual);
    }
    else if (isPowerType(formal) && isPowerType(actual)) {
      PowerType formalPower = (PowerType) formal;
      PowerType actualPower = (PowerType) actual;
      if (!isVariableType(formalPower.getType()) &&
          !isVariableType(actualPower.getType())) {
        result = typesUnify(formalPower.getType(), actualPower.getType());
      }
    }
    else if (isGivenType(formal) && isGivenType(actual)) {
      result = true;
    }
    else if (isSchemaType(formal) && isSchemaType(actual)) {
      SchemaType formalSchema = (SchemaType) formal;
      SchemaType actualSchema = (SchemaType) actual;

      List formalPairs = formalSchema.getSignature().getNameTypePair();
      List actualPairs = actualSchema.getSignature().getNameTypePair();

      if (formalPairs.size() == actualPairs.size()) {

        for (int i = 0; i < formalPairs.size(); i++) {
          NameTypePair formalPair = (NameTypePair) formalPairs.get(i);
          NameTypePair actualPair = (NameTypePair) actualPairs.get(i);

          if (formalPair.getName().equals(actualPair.getName())) {
            result = typesUnify(formalPair.getType(), actualPair.getType());
            if (!result) break;
          }
        }
      }
    }
    else if (isProdType(formal) && isProdType(actual)) {
      ProdType formalProd = (ProdType) formal;
      ProdType actualProd = (ProdType) actual;

      if (formalProd.getType().size() == actualProd.getType().size()) {

        for (int i = 0; i < formalProd.getType().size(); i++) {
          Type formalNext = (Type) formalProd.getType().get(i);
          Type actualNext = (Type) actualProd.getType().get(i);
          result = typesUnify(formalNext, actualNext);
          if (!result) break;
        }
      }
      else {
        result = false;
      }
    }
    else {
      result = false;
    }

    return result;
  }

  //returns true if and only if the two types are equal.
  protected static boolean typesEqual(Type type1, Type type2)
  {
    boolean result = false;

    if (type1.equals(type2)) {
      result = true;
    }
    else if (isPowerType(type1) && isPowerType(type2)) {
      //the case where one or both types are the empty set
      PowerType powerType1 = (PowerType) type1;
      PowerType powerType2 = (PowerType) type2;
      result = (isVariableType(powerType1.getType()) ||
                isVariableType(powerType2.getType()));
    }

    return result;
  }


  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown.
   */
  public static Type getBaseType(Type type)
  {
    Type result = UnknownTypeImpl.create();

    //if it's a PowerType, get the base type
    if (isPowerType(type)) {
      PowerType powerType = (PowerType) type;
      result = powerType.getType();
    }
    else if (isUnknownType(type)) {
      result = type;
    }
    return result;
  }

  public static Type getTypeFromAnns(TermA termA)
  {
    Type result = UnknownTypeImpl.create();

    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next instanceof TypeAnn) {
        result = ((TypeAnn) next).getType();
        break;
      }
    }

    return result;
  }

  /**
   * Adds an annotation to a term.
   */
  public TermA addAnns(TermA host, Term ann)
  {
    List list = ((TermA) host).getAnns();
    list.add(ann);
    return (TermA) host;
  }

  /**
   * Adds a type annotation to a term.
   */
  public TermA addAnns(TermA host, Type type)
  {
    List list = host.getAnns();
    TypeAnn  ta = makeTypeAnn(type);
    list.add(ta);
    return host;
  }

  protected static boolean isSchemaType(Type type)
  {
    return (type instanceof SchemaType);
  }

  protected static boolean isPowerType(Type type)
  {
    return (type instanceof PowerType);
  }

  protected static boolean isGivenType(Type type)
  {
    return (type instanceof GivenType);
  }

  protected static boolean isGenericType(Type type)
  {
    return (type instanceof GenericType);
  }

  protected static boolean isGenParamType(Type type)
  {
    return (type instanceof GenParamType);
  }

  protected static boolean isProdType(Type type)
  {
    return (type instanceof ProdType);
  }

  protected static boolean isUnknownType(Type type)
  {
    return (type instanceof UnknownType);
  }

  protected static boolean isVariableType(Type type)
  {
    return (type instanceof VariableType);
  }

  //non-safe typecast
  protected static SchemaType schemaType(Type type)
  {
    return (SchemaType) type;
  }

  //non-safe typecast
  protected static PowerType powerType(Type type)
  {
    return (PowerType) type;
  }

  //non-safe typecast
  protected static GivenType givenType(Type type)
  {
    return (GivenType) type;
  }

  //non-safe typecast
  protected static GenericType genericType(Type type)
  {
    return (GenericType) type;
  }

  //non-safe typecast
  protected static GenParamType genParamType(Type type)
  {
    return (GenParamType) type;
  }

  //non-safe typecast
  protected static ProdType prodType(Type type)
  {
    return (ProdType) type;
  }

  //non-safe typecast
  protected static UnknownType unknownType(Type type)
  {
    return (UnknownType) type;
  }

  private TypeAnn makeTypeAnn(Type type)
  {
    TypeAnn ta = factory_.createTypeAnn(type);
    return ta;
  }

  //add an error to the list of error annotation
  protected void error(ErrorAnn errorAnn)
  {
    errors_.add(errorAnn);
  }

  //add an error to the list of error messages, and as an annotation
  //to the term
  protected void error(TermA termA, ErrorAnn errorAnn)
  {
    termA.getAnns().add(errorAnn);
    error(errorAnn);
  }

  protected List list()
  {
    return new ArrayList();
  }

  protected List list(Object o)
  {
    List result = list();
    result.add(o);
    return result;
  }

  protected List list(Object o1, Object o2)
  {
    List result = list(o1);
    result.add(o2);
    return result;
  }

  protected void debug(String message)
  {
    if (DEBUG) {
      System.err.println(message);
    }
  }

  //converts a Term to a string
  //used for debugging only
  protected String format(Term term)
  {
    StringWriter writer = new StringWriter();
    PrintUtils.printUnicode(term, writer, manager_);
    return writer.toString();
  }

  protected String formatType(Type type)
  {
    //TypeFormatter formatter = new TypeFormatter();
    //Expr expr = (Expr) type.accept(formatter);
    //return format(expr);
    return type.toString();
  }
}
