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
  private ZFactory factory_;

  //the environment recording a name, its type, and the section in
  //which it was declared
  protected SectTypeEnv sectTypeEnv_;

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv_;

  //the list of exceptions thrown by retrieving type info
  protected List errors_;

  //the factory for creating error messages
  protected ErrorFactory errorFactory_;

  //for storing the name of the current section
  private String sectName_;

  private SectionManager manager_;

  //the writer which to write messages and errors
  protected Writer writer_;

  protected final boolean DEBUG_ = false;

  public TypeChecker(SectionManager manager)
  {
    manager_ = manager;
    errorFactory_ = new ErrorFactoryEnglish(manager);
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    sectName_ = null;
    sectTypeEnv_ = null;
    errors_ = list();
    unificationEnv_ = new UnificationEnv();
    writer_ = new PrintWriter(System.err);
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
	  String message = errorFactory_.redeclaredSection(zSect.getName());
	  exception(message);
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
	String message = errorFactory_.redeclaredParent(parent, sectName_);
	exception(message);
      }
      else if (parent.getWord().equals(sectName_)) {
       	String message = errorFactory_.selfParent(sectName_);
	exception(message);
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

    //print any exceptions
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
	String message = errorFactory_.strokeInGiven(declName);
	exception(message);
      }
      else if (names.contains(declName.getWord())) {
	String message = errorFactory_.redeclaredGiven(declName);
	exception(message);
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
	String message = errorFactory_.strokeInGen(declName);
	exception(message);
      }
      else if (names.contains(declName.getWord())) {
	String message = errorFactory_.redeclaredGen(declName);
	exception(message);
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

      if (type instanceof UnknownType) {
	String message = errorFactory_.unknownType(expr);
	exception(message);
      }
      else if (! (type instanceof PowerType)) {
	String message = errorFactory_.nonSetInFreeType(expr, type);
	exception(message);
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
	String message = errorFactory_.strokeInGen(declName);
	exception(message);
      }
      else if (names.contains(declName.getWord())) {
	String message = errorFactory_.redeclaredGen(declName);
	exception(message);
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
    if (type instanceof UnknownType) {
      String message = errorFactory_.unknownType(expr);
      exception(message);
    }
    else if (! (type instanceof PowerType)) {
      String message = errorFactory_.nonSetInDecl(expr, type);
      exception(message);
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
    if (! (exprType instanceof SchemaType)) {
      String message = errorFactory_.nonSchExprInInclDecl(inclDecl);
      exception(message);
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
      expr.accept(this);
    }

    return null;
  }

  // 13.2.6.5
  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    Expr expr = powerExpr.getExpr();
    expr.accept(this);

    Type type = getTypeFromAnns(expr);
    if (type instanceof UnknownType) {
      String message = errorFactory_.unknownType(expr);
      exception(message);
    }
    else if (! (type instanceof PowerType)) {
      String message = errorFactory_.nonSetInPowerExpr(powerExpr, type);
      exception(message);
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
	  String message =
	    errorFactory_.typeMismatchInSetExpr(expr, exprType, baseType);
	  exception(message);
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
    if (exprType instanceof UnknownType) {
      String message = errorFactory_.unknownType(expr);
      exception(message);
    }
    //if the type is not a cross product, report an error
    else if (! (exprType instanceof ProdType)) {
      String message =
	errorFactory_.nonProdTypeInTupleSelExpr(tupleSelExpr, exprType);
      exception(message);
    }
    else {
      //if the selection index is less than 1, or greater than the
      //the tuple length, report an error
      ProdType prodType = (ProdType) exprType;
      if (tupleSelExpr.getSelect().intValue() > prodType.getType().size() ||
	  tupleSelExpr.getSelect().intValue() < 1) {

	String message =
	  errorFactory_.indexErrorInTupleSelExpr(tupleSelExpr, prodType);
	exception(message);
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
      String message =
	errorFactory_.typeMismatchInCondExpr(condExpr, leftExprType, rightExprType);
      exception(message);
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
	String message =
	  errorFactory_.duplicateInBindExpr(bindExpr, nameExprPair.getName());
	exception(message);
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
    if (! (baseType instanceof SchemaType)) {
      String message =
	errorFactory_.nonSchExprInThetaExpr(thetaExpr, exprType);
      exception(message);    
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
    if (!(exprType instanceof SchemaType)) {
      String message =
	errorFactory_.nonSchTypeInBindSelExpr(bindSelExpr, exprType);
      exception(message);
    }
    else {
      //check that the selection is a valid name
      SchemaType schemaType = (SchemaType) exprType;
      RefName refName = bindSelExpr.getName();
      boolean found = false;
      for (Iterator iter = schemaType.getSignature().getNameTypePair().iterator();
	   iter.hasNext(); ) {
	NameTypePair nameTypePair = (NameTypePair) iter.next();
	if (refName.getWord().equals(nameTypePair.getName().getWord()) &&
	    refName.getStroke().equals(nameTypePair.getName().getStroke())) {
	  found = true;
	}
      }

      if (!found) {
	String message =
	  errorFactory_.nonExistentSelection(bindSelExpr, exprType);
	exception(message);
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
    if (! (leftBaseType instanceof ProdType) ||
	! (((ProdType) leftBaseType).getType().size() == 2)) {

      String message = errorFactory_.nonFunctionInApplExpr(applExpr, leftType);
      exception(message);
    }
    else {
      ProdType leftProdType = (ProdType) leftBaseType;
      Type firstType = (Type) leftProdType.getType().get(0);

      unificationEnv_.enterScope();
      if (!typesUnify(firstType, rightType)) {
	String message =
	  errorFactory_.typeMismatchInApplExpr(applExpr, firstType, rightType);
	exception(message);
      }
      unificationEnv_.exitScope();
    }

    return null;
  }

  ///// predicates /////////

  /**
   * Exists1Pred, ExistsPred, and ForallPred instances are
   * visited as an instance of their super class QntPred
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
   * visited as an instance of their super class Pred2
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
	String message =
	  errorFactory_.typeMismatchInEquality(memPred, leftType, rightBaseType);
	exception(message);
      }
    }
    //if this is a membership
    else if (!mixfix) {
      if (!typesEqual(leftType, rightBaseType)) {
	String message =
	  errorFactory_.typeMismatchInMemPred(memPred, leftType, rightType);
	exception(message);
      }      
    }
    //if it a relation other than equals or membership
    else {
      unificationEnv_.enterScope();
      if (!typesUnify(rightBaseType, leftType)) {
	String message =
	  errorFactory_.typeMismatchInRelOp(memPred, leftType, rightBaseType);	
	exception(message);
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

    if (formal instanceof GenType) {
      GenType formalGen = (GenType) formal;
      result = unificationEnv_.add(formalGen.getName(), actual);
    }
    else if (formal instanceof PowerType && actual instanceof PowerType) {
      PowerType formalPower = (PowerType) formal;
      PowerType actualPower = (PowerType) actual;
      if (formalPower.getType() != null && actualPower.getType() != null) {
        result = typesUnify(formalPower.getType(), actualPower.getType());
      }
    }
    else if (formal instanceof GivenType && actual instanceof GivenType) {
      result = true;
    }
    else if (formal instanceof SchemaType && actual instanceof SchemaType) {
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
    else if (formal instanceof ProdType && actual instanceof ProdType) {
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

  //returns true if and only if the two types are equal
  protected static boolean typesEqual(Type type1, Type type2)
  {
    boolean result = false;

    if (type1.equals(type2)) {
      result = true;
    }
    else if (type1 instanceof PowerType && type2 instanceof PowerType) {
      //the case where one or both types are the empty set
      PowerType powerType1 = (PowerType) type1;
      PowerType powerType2 = (PowerType) type2;
      result = (powerType1.getType() == null || powerType2.getType() == null);
    }

    return result;
  }


  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown
   */
  public static Type getBaseType(Type type)
  {
    Type result = UnknownTypeImpl.create();

    //if it's a PowerType, get the base type
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      result = powerType.getType();
    }
    else if (type instanceof UnknownType) {
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
   * Adds annotation (mainly type ann) to a TermA.
   */
  public TermA addAnns(TermA host, Term ann)
  {
    List list = ((TermA) host).getAnns();
    list.add(ann);
    return (TermA) host;
  }

  public TermA addAnns(TermA host, Type type)
  {
    List list = host.getAnns();
    TypeAnn  ta = makeTypeAnn(type);
    list.add(ta);
    return host;
  }

  private TypeAnn makeTypeAnn(Type type)
  {
    TypeAnn ta = factory_.createTypeAnn(type);
    return ta;
  }

  public ZFactory getFactory()
  {
    return factory_;
  }

  public SectTypeEnv getSectTypeEnv()
  {
    return sectTypeEnv_;
  }

  protected void exception(String message)
  {
    errors_.add(message);
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

  protected void debug(Exception e)
  {
    debug(e.toString());
  }

  protected void debug(String message)
  {
    if (DEBUG_) {
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
