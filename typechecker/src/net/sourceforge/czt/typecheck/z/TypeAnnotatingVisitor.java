package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Vector;
import java.util.Iterator;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;

import net.sourceforge.czt.typecheck.typeinference.z.*;

/**
 * A <code>TypeAnnotatingVisitor</code> visits an AST and adds type
 * annotations to the terms in this AST.  In this class, only some
 * visit methods return non-null objects: 
 *
 * - all visit methods to Expr objects return the type of the
 * expression
 *
 * - all visit methods to Decl objects return a list of NameTypePair
 * objects indicating the variables and their types declared in that
 * Decl.
 *
 * - the visit method for SchText return the signature of that object
 */
public class TypeAnnotatingVisitor  
  implements SpecVisitor,
             ZSectVisitor,
             ParentVisitor,
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
	     HideExprVisitor,
	     ProjExprVisitor,
	     PreExprVisitor,

	     QntPredVisitor,
	     Pred2Visitor,
	     MemPredVisitor,
	     NegPredVisitor,
	     ExprPredVisitor,
	     Visitor
{
  //a ZFactory for creating Z terms
  protected ZFactory factory_;

  //the list of exceptions thrown by retrieving type info
  protected List exceptions_;

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv_;

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv_;

  //for storing the name of the current section
  protected String section_;

  //true if and only if the current SchText should add
  //its declarations as global
  protected boolean global_ = false;

  //print debugging info
  protected static boolean DEBUG_ = true;

  public TypeAnnotatingVisitor (SectTypeEnv sectTypeEnv)
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    exceptions_ = list();
    sectTypeEnv_ = sectTypeEnv;
    typeEnv_ = new TypeEnv();
    section_ = null;
  }

  public Object visitSpec(Spec spec)
  {
    List sects = spec.getSect();
    for (Iterator iter = sects.iterator(); iter.hasNext(); ) {
      Sect sect = (Sect) iter.next();
      sect.accept(this);

      //annotate this section with the type info from this section
      //and its parents
      addAnns(sect, sectTypeEnv_.getSectTypeEnvAnn());
    }

    //print any exceptions
    for (Iterator iter = exceptions_.iterator(); iter.hasNext(); ) {
      Exception e = (Exception) iter.next();
      e.printStackTrace();
    }

    sectTypeEnv_.dump();
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    debug("ZSect name is: " + zSect.getName());

    //set this at the new section
    sectTypeEnv_.setSection(zSect.getName());

    //get and visit the parent sections of the current section
    List parents = zSect.getParent();
    for (Iterator iter = parents.iterator(); iter.hasNext(); ) {
      Parent parent = (Parent) iter.next();
      parent.accept(this);
    }

    //get and visit the paragraphs of the current section
    List paras = zSect.getPara();
    for (Iterator iter = paras.iterator(); iter.hasNext(); ) {
      Para para = (Para) iter.next();
      para.accept(this);
    }
    return null;
  }

  public Object visitParent(Parent parent)
  {
    debug("parent: " + parent.getWord());

    sectTypeEnv_.addParent(parent.getWord());

    /*
    try {
      //TODO: implement a utils package as in the parser!
      TypeCheckingUtils.typecheck(parent.getWord());
    }
    catch (TypeException e) {
      debug(e.toString() + "\n" + "Source: " + parent.getWord());
    }
    */
    return null;
  }

  //// paragraphs ////////

  public Object visitGivenPara(GivenPara givenPara)
  {
    debug("visiting GivenPara");

    //check for duplicates in the paragraph
    checkForDuplicates(givenPara.getDeclName());

    //the list of NameTypePairs for this paras signature
    List nameTypePairs = list();

    //get each DeclName
    List declNames = givenPara.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      //we don't visit these DeclNames because given types 
      //have a unique type inference rule
      GivenType givenType = factory_.createGivenType(declName);
      PowerType powerType = factory_.createPowerType(givenType);
      addAnns(declName, powerType);

      //add this to the SectTypeEnv
      sectTypeEnv_.add(declName, powerType);

      //add the NameTypePair to the list for the signature
      NameTypePair nameTypePair =
        factory_.createNameTypePair(declName, powerType);
      nameTypePairs.add(nameTypePair);
    }

    //create the signature for this paragraph and add it as 
    //an annotation
    Signature signature = factory_.createSignature(nameTypePairs);
    addAnns(givenPara, signature);

    return null;
  }

  public Object visitAxPara(AxPara axPara)
  {
    debug("visiting AxPara");

    //we enter a new variable scope for the generic parameters
    typeEnv_.enterScope();

    //add the names to the local type env
    addGenTypes(axPara.getDeclName());

    //get and visit the SchText, and add its declarations to
    //the SectTypeEnv
    global_ = true;
    SchText schText = axPara.getSchText();
    Signature signature = (Signature) schText.accept(this);

    //add the SchText signature as an annotation to this paragraph
    addAnns(axPara, signature);

    //exit the variable scope
    typeEnv_.exitScope();

    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    //the list of NameTypePairs for this paras signature
    List nameTypePairs = list();

    //visit each Freetype
    List freetypes = freePara.getFreetype();
    for (Iterator iter = freetypes.iterator(); iter.hasNext(); ) {
      Freetype freetype = (Freetype) iter.next();
      nameTypePairs.addAll((List) freetype.accept(this));
    }

    //create the signature for this paragraph and add it as 
    //an annotation
    Signature signature = factory_.createSignature(nameTypePairs);
    addAnns(freePara, signature);

    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    //the list of NameTypePairs for freetype's parent's signature
    List nameTypePairs = list();

    //the type of the Freetype's DeclName is a powerset of the
    //given type of itself
    DeclName declName = freetype.getDeclName();
    GivenType givenType = factory_.createGivenType(declName);
    PowerType powerType = factory_.createPowerType(givenType);

    //add this to the SectTypeEnv
    NameTypePair nameTypePair =
      factory_.createNameTypePair(declName, powerType);
    nameTypePairs.add(nameTypePair);

    //add this to the SectTypeEnv
    sectTypeEnv_.add(declName, powerType);

    //we don't visit the branches with their a "proper" visit method
    //because we need to pass the type of the DeclName
    List branches = freetype.getBranch();
    for (Iterator iter = branches.iterator(); iter.hasNext(); ) {
      Branch branch = (Branch) iter.next();
      nameTypePair = localVisitBranch(branch, givenType);
      nameTypePairs.add(nameTypePair);

      //add this pair to the SectTypeEnv
      sectTypeEnv_.add(nameTypePair);
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
      Type exprType = (Type) expr.accept(this);
      Type exprElementType = (Type) SectTypeEnv.getElementType(exprType);
      ProdType prodType =
	factory_.createProdType(list(exprElementType, givenType));
      PowerType powerType =
	factory_.createPowerType(prodType);

      nameTypePair = factory_.createNameTypePair(declName, powerType);
    }
    else {
      nameTypePair = factory_.createNameTypePair(declName, givenType);
    }

    return nameTypePair;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    //enter a new variable scope
    typeEnv_.enterScope();

    //add the generic types
    addGenTypes(conjPara.getDeclName());

    //visit the predicate
    Pred pred = conjPara.getPred();
    pred.accept(this);

    //the annotation for a conjecture paragraph is an empty signature
    Signature signature = factory_.createSignature();
    addAnns(conjPara, signature);

    //exit the variable scope
    typeEnv_.exitScope();

    return null;
  }

  public Object visitSchText(SchText schText)
  {
    //the list of NameType pairs declared in this schema text
    List nameTypePairs = list();

    //get and visit the list of declarations
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      nameTypePairs.addAll((List) decl.accept(this));
    }

    //add the declarations to the environment if this SchText
    //is in a global environment
    if (global_) {
      sectTypeEnv_.add(nameTypePairs);
    }
    //otherwise add them to the current TypeEnv
    else {
      typeEnv_.add(nameTypePairs);
    }

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      pred.accept(this);
    }

    //the signature for this schema text
    Signature signature = factory_.createSignature(nameTypePairs);

    //add this as a type annotation
    addAnns(schText, signature);

    return signature;
  }

  public Object visitVarDecl(VarDecl varDecl)
  {
    //the list of name type pairs in this VarDecl
    List nameTypePairs = list();

    //get and visit the expression
    Expr expr = varDecl.getExpr();
    Type superType = (Type) expr.accept(this);

    //the type of this variable
    Type type = SectTypeEnv.getElementType(superType);

    //get and visit the DeclNames
    List declNames = varDecl.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      //add the name and its type to the list of NameTypePairs
      NameTypePair nameTypePair =
	factory_.createNameTypePair(declName, type);
      nameTypePairs.add(nameTypePair);

      debug("vardecl name = " + declName.getWord() + " type = " + 
	    SectTypeEnv.toString(type));
      debug("\t superType = " + SectTypeEnv.toString(superType));
    }

    //according to section 10.2, this should have a type annotation.
    //But what is it?
    //addAnns(varDecl, ???);

    return nameTypePairs;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    debug("visiting ConstDecl");

    //the list of name type pairs in this ConstDecl
    //(this list will have only one element)
    List nameTypePairs = list();

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type type = (Type) expr.accept(this);

    //get the DeclName
    DeclName declName = constDecl.getDeclName();

    //create the NameTypePair and add it to the list
    NameTypePair nameTypePair =
      factory_.createNameTypePair(declName, type);
    nameTypePairs.add(nameTypePair);

    return nameTypePairs;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    debug("visiting InclDecl");

    //the list of name type pairs in this InclDecl
    List nameTypePairs = list();

    //get the expression
    Expr expr = inclDecl.getExpr();
    Type exprType = (Type) expr.accept(this);
    Type elementType = SectTypeEnv.getElementType(exprType);

    if (elementType instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) elementType;
      nameTypePairs.addAll(schemaType.getSignature().getNameTypePair());
    }
    //if the element type is not a SchemaType, then complain
    else {
      TypeException e =
	new TypeException(ErrorKind.SCHEXPR_EXPECTED, inclDecl);
      exceptions_.add(e);
    }

    return nameTypePairs;
  }

  //TODO: complete this for the case when the instantion list
  //is non-empty
  public Object visitRefExpr(RefExpr refExpr)
  {
    Type type = null;

    if (refExpr.getExpr().size() == 0) {
      RefName refName = refExpr.getRefName();
      type = getType(refName);
    }

    //add the type as an annotation
    addAnns(refExpr, type);

    return type;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    //get the expr and its type
    Expr expr = powerExpr.getExpr();
    Type nestedType = (Type) expr.accept(this);

    //if the inner expr is not a valid expr
    Type elementType = null;
    try {
      elementType = SectTypeEnv.getElementType(nestedType);
    }
    catch (TypeException e) {
      e.setTerm1(powerExpr);
      throw e;
    }

    //the type of a PowerExpr is the set of sets of the
    //types inside the PowerExpr
    PowerType innerType =
      factory_.createPowerType(elementType);
    PowerType type =
      factory_.createPowerType(innerType);

    //add the type as an annotation
    addAnns(powerExpr, type);

    return type;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    //the list of types in the expr
    List types = list();

    //get and visit the list of expressions
    List exprs = prodExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type nestedType = (Type) expr.accept(this);
      Type elementType = SectTypeEnv.getElementType(nestedType);
      types.add(elementType);
    }

    Type prodType = factory_.createProdType(types);
    Type type = factory_.createPowerType(prodType);

    //add the type as an annotation
    addAnns(prodExpr, type);

    return type;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    Type innerType = new VariableType();

    //get and visit each expression
    List exprs = setExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type nestedType = (Type) expr.accept(this);

      //find a type of the inner expr. The typechecker will deal
      //with the condition that all types in the set are the same
      if (innerType instanceof VariableType) {
	innerType = nestedType;
      }
    }

    //the type of a set expression is a power set of the
    //types inside the SetExpr
    Type type = factory_.createPowerType(innerType);

    //add the type as an annotion
    addAnns(setExpr, type);

    return type;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    //the type of a NumExpr is the given type arithmos
    DeclName declName =
      factory_.createDeclName(ZString.ARITHMOS, list(), null);
    Type type = factory_.createGivenType(declName);

    //add the type as an annotation
    addAnns(numExpr, type);

    return type;
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    //visit the SchText and add return the signature
    //from that as the signature for this expression
    global_ = false;
    SchText schText = schExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = true;

    SchemaType schemaType = factory_.createSchemaType(signature);
    PowerType type = factory_.createPowerType(schemaType);

    //add the type annotation
    addAnns(schExpr, type);

    return type;
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    //the type of the overall expression
    Type type = null;

    //enter a new variable scope
    typeEnv_.enterScope();

    //get the signature from the SchText
    global_ = false;
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
      types.add(nextType);
      
      //add this pair to the TypeEnv
      typeEnv_.add(pair);
    }

    //if the expr is null, then use the signature to obtain the type
    if (expr == null) {

      //if the is only one element, then the type is a power set
      //of the type of that element
      if (types.size() == 1) {
	Type innerType = (Type) types.get(0);
	type = factory_.createPowerType(innerType);
      }
      //otherwise, create a ProdType
      else {
	ProdType prodType = factory_.createProdType(types);
	type = factory_.createPowerType(prodType);
      }
    }
    //if the expr is not null, then the overall type is a power set
    //of the type of expr
    else {
      Type exprType = (Type) expr.accept(this);
      type = factory_.createPowerType(exprType);
    }

    //exit the variable scope
    typeEnv_.exitScope();

    //add the type annotation
    addAnns(setCompExpr, type);

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
    ProdType type = factory_.createProdType(types);

    //add the type annotations
    addAnns(tupleExpr, type);

    return type;
  }

  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    //the type of this expression
    Type type = null;

    //get the types of the expression
    Expr expr = tupleSelExpr.getExpr();
    Type exprType = (Type) expr.accept(this);

    //if the expression is a ProdType, then find the type
    //of the selection
    if (exprType instanceof ProdType) {
      ProdType prodType = (ProdType) exprType;

      //if the selection is greater than the length
      //then complain
      int index = tupleSelExpr.getSelect().intValue();
      if (index > prodType.getType().size()) {

	String message = "size = " + prodType.getType().size() + "; " +
	  "selection = " + index;
	TypeException e =
	  new TypeException(ErrorKind.TUPLESELEXPR_OUT_OF_RANGE, expr);
	exceptions_.add(e);
      }
      //otherwise, get the type of the expression at index
      else {
	type = (Type) prodType.getType().get(index - 1);
      }
    }
    //if it is not a ProdType, then complain
    else {
      TypeException e =
	new TypeException(ErrorKind.PRODTYPE_REQUIRED, expr);
      exceptions_.add(e);
    }

    //add the type annotation
    addAnns(tupleSelExpr, type);

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
    Type type = UnknownTypeImpl.create();

    //visit the SchText, but do not add its declarations
    //as global
    boolean oldGlobal = global_;
    global_ = false;
    SchText schText = qnt1Expr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = oldGlobal;

    Expr expr = qnt1Expr.getExpr();    

    Type exprType = (Type) expr.accept(this);
    Type elementType = SectTypeEnv.getElementType(exprType);

    //if the type of expr is a schema, then assign the type by
    //substracting schText's signature from expr's signature
    if (elementType instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) elementType;
      Signature qnt1ExprSignature =
	schemaHide(schemaType.getSignature(), signature);
      type = factory_.createSchemaType(qnt1ExprSignature);
    }
    //if it is not a SchemaType, then complain
    else {
      TypeException e =
	new TypeException(ErrorKind.SCHEXPR_EXPECTED, expr);
      exceptions_.add(e);
    }    

    //add the type annotation
    addAnns(qnt1Expr, type);

    return type;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    //get the signature of the SchText
    boolean oldGlobal = global_;
    global_ = false;
    SchText schText = lambdaExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = oldGlobal;

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
	charTupleList.add(nameTypePair.getType());
      }

      charTuple = factory_.createProdType(charTupleList);
    }
    //otherwise, the characterisitic tuple is the type of the only decl
    else {
      NameTypePair nameTypePair =
	(NameTypePair) signature.getNameTypePair().get(0);
      charTuple = nameTypePair.getType();
    }

    //the type of the expression is a power set of the cross product
    //of the characteristic tuple of the schema text, and the type of
    //the expression
    ProdType prodType =
      factory_.createProdType(list(charTuple, exprType));
    PowerType type = factory_.createPowerType(prodType);

    //add the type annotation
    addAnns(lambdaExpr, type);
    
    return type;
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    return visitMuOrLetExpr(muExpr);
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    return visitMuOrLetExpr(letExpr);
  }

  //a 'let' expression is easily transformed to a 'mu' expression, so
  //we visit them with  the same method
  private Object visitMuOrLetExpr(Expr muOrLetExpr)
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
    boolean oldGlobal = global_;
    global_ = false;
    schText.accept(this);
    global_ = oldGlobal;

    //get the type of the expression, which is also the type
    //of the entire expression (the MuExpr or LetExpr);
    Type type = (Type) expr.accept(this);

    //add the type annotation
    addAnns(muOrLetExpr, type);

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
    Type type = UnknownTypeImpl.create();

    //get the types of the left and right expressions
    Expr leftExpr = schExpr2.getLeftExpr();
    Expr rightExpr = schExpr2.getRightExpr();
    Type leftType = (Type) leftExpr.accept(this);
    Type rightType = (Type) rightExpr.accept(this);

    //get the element types of the expressions
    Type leftElementType = SectTypeEnv.getElementType(leftType);
    Type rightElementType = SectTypeEnv.getElementType(rightType);

    //if the left or right expressions are not schemas
    if (!(leftElementType instanceof SchemaType)) {
      TypeException e =
	new TypeException(ErrorKind.SCHEXPR_EXPECTED, leftExpr);
      exceptions_.add(e);
      return type;
    }

    if (!(rightElementType instanceof SchemaType)) {
      TypeException e =
	new TypeException(ErrorKind.SCHEXPR_EXPECTED, rightExpr);
      exceptions_.add(e);
      return type;
    }

    //check that the signatures are compatible
    Signature leftSig = ((SchemaType) leftElementType).getSignature();
    Signature rightSig = ((SchemaType) rightElementType).getSignature();
    if (!signaturesCompatible(leftSig, rightSig)) {
      return type;
    }

    //the type is a power set of a schema that has the union of the
    //two signatures
    Signature signature = unionSignatures(leftSig, rightSig);
    SchemaType schemaType = factory_.createSchemaType(signature);
    type = factory_.createPowerType(schemaType);

    //add the type annotation
    addAnns(schExpr2, type);

    return type;
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    //get the type of the expr, which is the type of the 
    //overall expr
    Expr expr = negExpr.getExpr();
    Type type = (Type) expr.accept(this);

    //add the type annotation
    addAnns(negExpr, type);

    return type;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    //visit the Pred
    Pred pred = condExpr.getPred();
    pred.accept(this);

    //get the type of the left and right expr
    Expr leftExpr = condExpr.getLeftExpr();
    Expr rightExpr = condExpr.getRightExpr();
    Type leftType = (Type) leftExpr.accept(this);
    Type rightType = (Type) rightExpr.accept(this);

    //add the type annotation. We simply use the type of the left
    //expr. If the left and right expr have different types, the
    //typechecker will deal with this
    addAnns(condExpr, leftType);

    return leftType;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    //the type of this expression
    Type type = UnknownTypeImpl.create();    
    /*
    //if the left and right expressions are schemas, and the
    //signatures are compatible
    if (checkLeftRightSchema(compExpr)) {

      SchemaType leftType = getSchemaType(compExpr.getLeftExpr());
      SchemaType rightType = getSchemaType(compExpr.getRightExpr());

      Signature primedType = decorate(leftType.getSignature(),
				      factory_.createNextStroke());

      //signaturesCompatible(compExpr);

    }
    */
    //add the type annotation
    addAnns(compExpr, type);

    return type;
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    Type type = UnknownTypeImpl.create();

    Expr expr = hideExpr.getExpr();
    expr.accept(this);

    if (checkSchema(expr)) {

      //hide the declarations
      SchemaType schemaType = getSchemaType(expr);
      Signature signature = schemaHide(schemaType.getSignature(),
				       hideExpr.getName());
      type = factory_.createSchemaType(signature);
    }

    //add the type annotation
    addAnns(hideExpr, type);

    return type;
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    //visit the left and right exprs. The type of this whole
    //expression is the type of the right expr
    Expr leftExpr = projExpr.getLeftExpr();
    Expr rightExpr = projExpr.getRightExpr();
    leftExpr.accept(this);
    Type type = (Type) rightExpr.accept(this);

    //add the type annotation
    addAnns(projExpr, type);

    return type;
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    //the type of this expression
    Type type = UnknownTypeImpl.create();

    //visit the expression
    Expr expr = preExpr.getExpr();
    expr.accept(this);

    //the type of the expression is the same a preExpr, with all
    //primed and shrieked variables hidden
    if (checkSchema(expr)) {

      SchemaType preSchemaType = getSchemaType(expr);

      NextStroke nextStroke = factory_.createNextStroke();
      OutStroke outStroke = factory_.createOutStroke();

      //the list of NameTypePairs for the new signature
      List nameTypePairs = list();
      for (Iterator iter =
	     preSchemaType.getSignature().getNameTypePair().iterator();
	   iter.hasNext(); ) {
	NameTypePair nameTypePair = (NameTypePair) iter.next();

	//the strokes of this name
	List strokes = nameTypePair.getName().getStroke();

	//if the last stroke is not a prime or shriek, then add
	//to the new signature
	if (strokes.size() == 0 ||
	    (strokes.size() > 0 &&
	     !(strokes.get(0).equals(nextStroke) ||
	       strokes.get(0).equals(outStroke)))) {

	  nameTypePairs.add(nameTypePair);
	}

      }

      Signature signature = factory_.createSignature(nameTypePairs);
      SchemaType schemaType = factory_.createSchemaType(signature);
      type = factory_.createPowerType(schemaType);
    }

    //add the type annotation
    addAnns(preExpr, type);

    return type;
  }

  public Object visitThetaExpr(ThetaExpr term)
  {
    Type type = null;
    return type;
  }

  ///// predicates /////////

  /**
   * Exists1Pred, ExistsPred, and ForallPred instances are
   * visited as an instance of their super class QntPred
   */
  public Object visitQntPred(QntPred qntPred)
  {
    //enter a new variable scope
    typeEnv_.enterScope();

    //visit the SchText
    global_ = false;
    SchText schText = qntPred.getSchText();
    schText.accept(this);

    //visit the Pred
    Pred pred = qntPred.getPred();
    pred.accept(this);

    //exit the variable scope
    typeEnv_.exitScope();

    return null;
  }

  /**
   * AndPred, IffPred, ImpliesPred, and OrPred instances  are
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

  public Object visitMemPred(MemPred memPred)
  {
    //visit the left and right expressions
    Expr leftExpr = memPred.getLeftExpr();
    leftExpr.accept(this);

    Expr rightExpr = memPred.getRightExpr();
    rightExpr.accept(this);

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

  //// helper methods /////

  //add generic types from a list of DeclNames to the TypeEnv
  protected void addGenTypes(List declNames)
  {
    //check for duplicates in the generic parameters
    checkForDuplicates(declNames);

    //add each DeclName and its type
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      //we don't visit these DeclNames because given types 
      //have a unique type inference rule
      GenType genType = factory_.createGenType(declName);
      PowerType powerType = factory_.createPowerType(genType);
      addAnns(declName, powerType);

      //add the name and type to the TypeEnv
      typeEnv_.add(declName, powerType);
    }
  }

  //gets the type of the expression represented by a name
  protected Type getType(Name name)
  {
    //get the type from the TypeEnv
    Type type = typeEnv_.getType(name);

    //if the TypeEnv did not know of this expression, then
    //ask the SectTypeEnv
    if (type instanceof UnknownType) {
      type = sectTypeEnv_.getType(name);
    }

    return type;
  }

  //check for duplicate names in a list of names
  protected void checkForDuplicates(List names)
  {
    for (int i = 0; i < names.size(); i++) {
      Name name1 = (Name) names.get(i);

      for (int j = 0; j < names.size(); j++) {
	if (i != j) {
	  Name name2 = (Name) names.get(j);

	  //if the 2 names are equal, add an exception to
	  //our exception list
	  if (name1.equals(name2)) {

	    String message = "Redeclared name: " + SectTypeEnv.toString(name1);
	    Exception e =
	      new TypeException(ErrorKind.REDECLARATION, name2, message);
	    exceptions_.add(e);
	  }
	}
      }
    }
  }

  //checks that the left and right expression of a Expr2 
  //have type 'power Schema'
  protected boolean checkLeftRightSchema(Expr2 expr2)
  {
    boolean result = true;

    //get the types of the left and right expressions
    Expr leftExpr = expr2.getLeftExpr();
    Expr rightExpr = expr2.getRightExpr();

    result = checkSchema(leftExpr) & checkSchema(rightExpr);

    return result;
  }
 
  //checks that the expr has the type 'power schema'
  protected boolean checkSchema(Expr expr)
  {
    boolean result = true;

    Type type = (Type) expr.accept(this);
    Type elementType =  SectTypeEnv.getElementType(type);

    if (!(elementType instanceof SchemaType)) {
      TypeException e =
	new TypeException(ErrorKind.SCHEXPR_EXPECTED, expr);
      exceptions_.add(e);
      result = false;
    }

    return result;
  }

  //precondition: both the left and right expr are of type Schema
  protected boolean signaturesCompatible(Expr2 expr2)
  {
    boolean result = true;

    //get the types of the left and right expressions
    Expr leftExpr = expr2.getLeftExpr();
    Expr rightExpr = expr2.getRightExpr();
    Type leftType = (Type) leftExpr.accept(this);
    Type rightType = (Type) rightExpr.accept(this);

    //get the element types of the expressions
    SchemaType leftElementType =
      (SchemaType) SectTypeEnv.getElementType(leftType);
    SchemaType rightElementType =
      (SchemaType) SectTypeEnv.getElementType(rightType);

    result = signaturesCompatible(leftElementType.getSignature(),
				  rightElementType.getSignature());

    return result;
  }

  protected boolean signaturesCompatible(Signature left,
					 Signature right)
  {
    boolean result = true;

    List leftNames = left.getNameTypePair();
    List rightNames = right.getNameTypePair();

    for (Iterator leftIter = leftNames.iterator(); leftIter.hasNext(); ) {
      NameTypePair leftPair = (NameTypePair) leftIter.next();

      for (Iterator rightIter = rightNames.iterator();
	   rightIter.hasNext(); ) {
	NameTypePair rightPair = (NameTypePair) rightIter.next();

	//complain if the types to not agree
	if (leftPair.getName().equals(rightPair.getName()) &&
	    !leftPair.getType().equals(rightPair.getType())) {

	  String message = "Incompatible for variable " + 
	    SectTypeEnv.toString(leftPair.getName());
	  TypeException e =
	    new TypeException(ErrorKind.INCOMPATIBLE_SIGNATURES,
			      left, right, message);
	  result = false;
	  break;
	}
      }

      if (!result) {
	break;
      }
    }
    return result;
  }

  //precondition: the type of 'expr' is a power set of a schema type
  protected SchemaType getSchemaType(Expr expr)
  {
    PowerType powerType = (PowerType) expr.accept(this);
    SchemaType schemaType = (SchemaType) powerType.getType();
    return schemaType;
  }

  //return a new signature with with each element decorated with
  //a specified stroke
  /*
  protected Signature decorate(Signature signature, Stroke stroke)
  {
    //the list of NameTypePairs for the new signature
    List nameTypePairs = list();

    for (Iterator iter = signature.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
    }
  }
  */

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

    Signature signature = factory_.createSignature(nameTypePairs);
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

    return factory_.createSignature(nameTypePairs);
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
	factory_.createRefName(nameTypePair.getName().getWord(),
			       nameTypePair.getName().getStroke(),
			       null);

      //only add the pair to the new signature if the name is not
      //being hidden
      if (!names.contains(refName)) {
	nameTypePairs.add(nameTypePair);
      }
    }

    //create the new signature
    Signature signature = factory_.createSignature(nameTypePairs);

    return signature;
  }

  protected NameTypePair findInSignature(DeclName declName, 
					 Signature signature)
  {
    NameTypePair result = null;

    for (Iterator iter = signature.getNameTypePair().iterator(); 
	 iter.hasNext(); ) {

      NameTypePair nameTypePair = (NameTypePair) iter.next();

      if (nameTypePair.getName().equals(declName)) {
	result = nameTypePair;
	break;
      }
    }

    return result;
  }

  //adds an annotation to a TermA
  protected void addAnns(TermA termA, Object ann)
  {
    if (ann != null) {
      termA.getAnns().add(ann);
    }
  }

  //adds a type annotation created from a given type to
  //a TermA
  //TODO: change this so that it replaces any existing type
  //annotations
  protected void addAnns(TermA termA, Type type)
  {
    if (type != null) {
      TypeAnn typeAnn =  factory_.createTypeAnn(type);
      addAnns(termA, typeAnn);
    }
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
    if (DEBUG_) {
      System.err.println(message);
    }
  }
}
