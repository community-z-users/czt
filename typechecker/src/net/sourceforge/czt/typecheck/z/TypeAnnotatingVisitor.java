package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.util.CztException;
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
 *
 * TODO: use the 'typesUnify' method from TypeChecker to check for type
 * equality
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

  //the factory for creating error messages
  protected ErrorFactory error_ = new ErrorFactoryEnglish();

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv_;

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv_;

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv_;

  //for storing the name of the current section
  protected String section_;

  //true if and only if the current SchText should add
  //its declarations as global
  protected boolean global_ = false;

  //print debugging info
  protected static boolean DEBUG_ = false;

  public TypeAnnotatingVisitor(SectTypeEnv sectTypeEnv)
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    exceptions_ = list();
    sectTypeEnv_ = sectTypeEnv;
    typeEnv_ = new TypeEnv();
    unificationEnv_ = new UnificationEnv();
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
      System.err.println(e.toString());
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

    //visit each Freetype again so that mutually recursive free types
    //can be supported
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
      Type exprBaseType = getBaseType(exprType);

      ProdType prodType =
	factory_.createProdType(list(exprBaseType, givenType));
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
    Type type = (Type) expr.accept(this);

    //the type of this variable
    Type baseType = getBaseType(type);

    //get and visit the DeclNames
    List declNames = varDecl.getDeclName();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();
      
      //add the name and its type to the list of NameTypePairs
      NameTypePair nameTypePair =
	factory_.createNameTypePair(declName, baseType);
      nameTypePairs.add(nameTypePair);
      
      debug("vardecl name = " + declName.getWord() + " type = " + 
	    SectTypeEnv.toString(baseType));
      
      if (type == null) {
	sectTypeEnv_.dump();
      }
      
      debug("\t superType = " + SectTypeEnv.toString(type));
    }

    //according to section 10.2, this should have a type annotation.
    //But what is it?
    //addAnns(varDecl, ???);

    return nameTypePairs;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    //the list of name type pairs in this ConstDecl
    //(this list will have only one element)
    List nameTypePairs = list();

    //get the DeclName
    DeclName declName = constDecl.getDeclName();

    //add a ParameterAnn to the name if there are any params
    if (typeEnv_.getParameters() != null &&
	typeEnv_.getParameters().size() > 0) {

      ParameterAnn parameterAnn =
	new ParameterAnn(typeEnv_.getParameters());
      addAnns(declName, parameterAnn);
    }

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type type = (Type) expr.accept(this);

    //create the NameTypePair and add it to the list
    NameTypePair nameTypePair =
      factory_.createNameTypePair(declName, type);
    nameTypePairs.add(nameTypePair);

    debug("visiting ConstDecl");
    debug("\tname = " + declName.getWord());
    debug("\t type = " + SectTypeEnv.toString(type));

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
    Type elementType = getBaseType(exprType);
    
    if (elementType instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) elementType;
      nameTypePairs.addAll(schemaType.getSignature().getNameTypePair());
    }

    return nameTypePairs;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    Type type = unknownType();

    RefName refName = refExpr.getRefName();
    Type refNameType = getType(refName);  

    List exprs = refExpr.getExpr();

    //if this is not a generic instantiation, then the type of refExpr
    //is the type of the whole expression
    if (exprs.size() == 0) {
      type = refNameType;
    }    
    else {
      debug("generic instantiation");

      //get the parameters associated with this name and
      //create GenTypes for them
      List params = sectTypeEnv_.getParameters(refName);
      List genTypes = list();
      for (Iterator iter = params.iterator(); iter.hasNext(); ) {
	DeclName declName = (DeclName) iter.next();
	GenType genType = factory_.createGenType(declName);	
	genTypes.add(genType);
      }

      if (genTypes.size() == exprs.size()) {

	//replace any references to generic types by the actual types in
	//the expression
	unificationEnv_.enterScope();

	Iterator exprIter = exprs.iterator();
	for (Iterator genIter = genTypes.iterator(); genIter.hasNext(); ) {
	  //get the next generic type
	  GenType genType = (GenType) genIter.next();

	  //get the type of the next expression
	  Expr expr = (Expr) exprIter.next();
	  Type exprType = (Type) expr.accept(this);
	  Type exprBaseType = getBaseType(exprType);

	  //unify the two
	  unificationEnv_.add(genType.getName(), exprBaseType);
	}

	//replace all references to generic types with their
	//unified counterparts
	type = replaceGenTypes(refNameType);

	unificationEnv_.exitScope();
      }
    }

    //add the type annotation
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
      elementType = getBaseType(nestedType);
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
    int position = 1;
    List exprs = prodExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); position++) {
      Expr expr = (Expr) iter.next();
      Type nestedType = (Type) expr.accept(this);
      Type elementType = getBaseType(nestedType);

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
    Type innerType = null;

    //get and visit each expression
    List exprs = setExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type nestedType = (Type) expr.accept(this);

      //find a type of the inner expr. The typechecker will deal
      //with the condition that all types in the set are the same
      if (innerType == null) {
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
    debug("visiting SetCompExpr");

    //the type of the overall expression
    Type type = null;

    //enter a new variable scope
    typeEnv_.enterScope();

    //get the signature from the SchText
    boolean oldGlobal = global_;
    global_ = false;
    SchText schText = setCompExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = oldGlobal;

    //get the expr
    Expr expr = setCompExpr.getExpr();

    //get the types from the signature
    List types = list();
    List nameTypePairs = signature.getNameTypePair();
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      Type nextType = pair.getType();
      types.add(nextType);
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
    Type type = unknownType();

    //get the types of the expression
    Expr expr = tupleSelExpr.getExpr();
    Type exprType = (Type) expr.accept(this);

    //if the expression is a ProdType, then find the type
    //of the selection
    if (exprType instanceof ProdType) {
      ProdType prodType = (ProdType) exprType;

      //get the type 
      int index = tupleSelExpr.getSelect().intValue();
      if (index <= prodType.getType().size()) {
	type = (Type) prodType.getType().get(index - 1);
      }
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
    Type type = unknownType();

    //visit the SchText, but do not add its declarations
    //as global
    boolean oldGlobal = global_;
    global_ = false;
    SchText schText = qnt1Expr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = oldGlobal;

    Expr expr = qnt1Expr.getExpr();    

    Type exprType = (Type) expr.accept(this);
    Type elementType = getBaseType(exprType);

    //if the type of expr is a schema, then assign the type by
    //substracting schText's signature from expr's signature
    if (elementType instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) elementType;
      Signature qnt1ExprSignature =
	schemaHide(schemaType.getSignature(), signature);
      type = factory_.createSchemaType(qnt1ExprSignature);
    }

    //add the type annotation
    addAnns(qnt1Expr, type);

    return type;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    debug("visiting LambdaExpr");

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
    Type type = null;

    //if the expr part of the expr is not null, then apply rule
    //13.9.6.12
    if (muExpr.getExpr() != null) {
      type = visitMuOrLetExpr(muExpr);
    }
    //otherwise, apply transformation rule C.6.37.2
    else {
      boolean oldGlobal = global_;
      global_ = false;
      SchText schText = muExpr.getSchText();
      //Signature signature = (Signature) schText.accept(this);
      global_ = oldGlobal;

      List exprList = list();
      for (Iterator iter = schText.getDecl().iterator();
	   iter.hasNext(); ) {

	//for each declaration, get the name and add it to the expr
	//part of the MuExpr
	Decl decl = (Decl) iter.next();
	List decls = (List) decl.accept(this);

	for (Iterator declIter = decls.iterator(); declIter.hasNext(); ) {

	  NameTypePair nameTypePair = (NameTypePair) declIter.next();
	  DeclName declName = nameTypePair.getName();
	  RefName refName = factory_.createRefName(declName.getWord(),
						   declName.getStroke(),
						   null);
	  RefExpr refExpr =
	    factory_.createRefExpr(refName, list(), Boolean.FALSE);
	  
	  exprList.add(refExpr);
	}
      }

      TupleExpr tupleExpr = factory_.createTupleExpr(exprList);

      MuExpr transformedMuExpr = factory_.createMuExpr(schText, tupleExpr);
      type = visitMuOrLetExpr(transformedMuExpr);
    }

    return type;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    return visitMuOrLetExpr(letExpr);
  }

  //a 'let' expression is easily transformed to a 'mu' expression, so
  //we visit them with  the same method
  private Type visitMuOrLetExpr(Expr muOrLetExpr)
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
    Type type = unknownType();

    //get the types of the left and right expressions
    Expr leftExpr = schExpr2.getLeftExpr();
    Expr rightExpr = schExpr2.getRightExpr();
    Type leftType = (Type) leftExpr.accept(this);
    Type rightType = (Type) rightExpr.accept(this);

    //get the element types of the expressions
    Type leftBaseType = getBaseType(leftType);
    Type rightBaseType = getBaseType(rightType);

    //if the left or right expressions are not schemas, then we cannot
    //get the type yet
    if (!(leftBaseType instanceof SchemaType)) {
      return type;
    }

    if (!(rightBaseType instanceof SchemaType)) {
      return type;
    }

    //check that the signatures are compatible
    Signature leftSig = ((SchemaType) leftBaseType).getSignature();
    Signature rightSig = ((SchemaType) rightBaseType).getSignature();
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
    Type type = unknownType();    

    /*
    //if the left and right expressions are schemas, and the
    //signatures are compatible
    if (leftRightAreSchemas(compExpr)) {

      SchemaType leftType = cloneType(getSchemaType(compExpr.getLeftExpr()));
      SchemaType rightType = cloneType(getSchemaType(compExpr.getRightExpr()));

      Signature primedLeftType =
	decorate(leftType, list(factory_.createNextStroke()));

    }
    */

    //add the type annotation
    addAnns(compExpr, type);

    throw new UnsupportedOperationException();

    //return type;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    throw new UnsupportedOperationException();
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    Type type = unknownType();

    //no need to visit the expr because isSchema will
    Expr expr = hideExpr.getExpr();

    if (isSchema(expr)) {

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
    Type type = unknownType();

    //no need to visit the expression because isSchema will
    Expr expr = preExpr.getExpr();

    //the type of the expression is the same a preExpr, with all
    //primed and shrieked variables hidden
    if (isSchema(expr)) {

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

  public Object visitApplExpr(ApplExpr applExpr)
  {
    debug("visiting ApplExpr, mixfix = " + applExpr.getMixfix());

    //the type of this expression
    Type type = unknownType();

    //get the type of the left and right expressions
    Expr leftExpr = applExpr.getLeftExpr();
    Expr rightExpr = applExpr.getRightExpr();
    Type leftType = (Type) leftExpr.accept(this);
    Type rightType = (Type) rightExpr.accept(this);

    if (leftExpr instanceof RefExpr) {
      String name = ((RefExpr) leftExpr).getRefName().getWord();
      debug("applExpr name = " + name);
    }
    debug("applexpr leftType = " + SectTypeEnv.toString(leftType));

    Type leftBaseType = getBaseType(leftType);

    //if the left expression is a power set of a cross product, then
    //the type of the second component is the type of the whole
    //expression
    if (leftBaseType instanceof ProdType &&
	((ProdType) leftBaseType).getType().size() == 2) {

      ProdType prodType = (ProdType) leftBaseType;

      debug("leftBaseType = " + SectTypeEnv.toString(leftBaseType));
      debug("rightType = " + SectTypeEnv.toString(rightType));

      unificationEnv_.enterScope();

      //replace any references to generic types by the actual types in
      //the expression
      if (unifyGenTypes((Type) prodType.getType().get(0), rightType)) {

	ProdType replaced = (ProdType) replaceGenTypes(prodType);

	//the type of the whole expression is the type of the second
	//expression in the cross product
	type = (Type) replaced.getType().get(1);
      }

      unificationEnv_.exitScope();
    }

    //add the type annotation
    addAnns(applExpr, type);

    return type;
  }

  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    Type type = null;

    //no need to visit the expr because isSchema will
    Expr expr = thetaExpr.getExpr();

    if (isSchema(expr)) {
      type = getSchemaType(expr);
    }

    //add the type annotation
    addAnns(thetaExpr, type);

    return type;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    debug("visiting DecorExpr");
    Type type = unknownType();

    //no need to visit the expression because isSchema will
    Expr expr = decorExpr.getExpr();

    //if the expr is a schema reference, decorate each name in the signature
    if (isSchema(expr)) {
      PowerType exprType = (PowerType) expr.accept(this);
      SchemaType schemaType = (SchemaType) exprType.getType();
      SchemaType decoratedSchemaType = 
	decorate(schemaType, decorExpr.getStroke());
      type = factory_.createPowerType(decoratedSchemaType);
    }

    //add the type annotation
    addAnns(decorExpr, type);

    return type;
  }

  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    debug("visiting RenameExpr");
    SchemaType type = null;

    //no need to visit the expression because isSchema will
    Expr expr = renameExpr.getExpr();

    //if the expr is a schema reference, decorate each name in the signature
    if (isSchema(expr)) {
      type = (SchemaType) cloneType(getSchemaType(expr));
      List nameTypePairs = type.getSignature().getNameTypePair();

      for (Iterator nameNameIter = renameExpr.getNameNamePair().iterator();
	   nameNameIter.hasNext(); ) {

	NameNamePair nameNamePair = (NameNamePair) nameNameIter.next();
        RefName oldName = nameNamePair.getOldName();

	for (Iterator nameTypeIter = nameTypePairs.iterator();
	     nameTypeIter.hasNext(); ) {

	  NameTypePair nameTypePair = (NameTypePair) nameTypeIter.next();
	  DeclName declaredName = nameTypePair.getName();

	  //if the old name is in the signature, replace it
	  //with the new name
	  if (declaredName.getWord().equals(oldName.getWord()) &&
	      declaredName.getStroke().equals(oldName.getStroke())) {

	    DeclName newName = nameNamePair.getNewName();

	    declaredName.setWord(newName.getWord());
	    declaredName.getStroke().clear();
	    declaredName.getStroke().addAll(newName.getStroke());
	  }
	}
      }
    }

    //add the type annotation
    addAnns(renameExpr, type);

    return type;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    Type type = unknownType();

    //get the type of the expression
    Expr expr = bindSelExpr.getExpr();
    Type exprType = (Type) expr.accept(this);

    //if expr is a binding, then get the type of the name
    if (exprType instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) exprType;
      RefName refName = bindSelExpr.getName();

      for (Iterator iter =
	     schemaType.getSignature().getNameTypePair().iterator();
	   iter.hasNext(); ) {
	NameTypePair nameTypePair = (NameTypePair) iter.next();
	DeclName declName = nameTypePair.getName();

	if (declName.getWord().equals(refName.getWord()) &&
	    declName.getStroke().equals(refName.getStroke())) {
	  type = nameTypePair.getType();
	  break;
	}
      }
    }

    //add the annotation
    addAnns(bindSelExpr, type);

    return type;
  }

  public Object visitBindExpr(BindExpr bindExpr)
  {
    Type type = unknownType();

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
	factory_.createNameTypePair(declName, exprType);
      nameTypePairs.add(nameTypePair);
    }

    //create the type
    Signature signature = factory_.createSignature(nameTypePairs);
    type = factory_.createSchemaType(signature);

    //add the type annotation
    addAnns(bindExpr, type);

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
    typeEnv_.setParameters(declNames);

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

  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown
   */
  public Type getBaseType(Type type)
    throws TypeException
  {
    Type result = unknownType();

    //if it's a PowerType, get the base type
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      result = powerType.getType();
    }

    return result;
  }


  //checks that the left and right expression of a Expr2 
  //have type 'power Schema'
  protected boolean leftRightAreSchemas(Expr2 expr2)
  {
    boolean result = true;

    //get the types of the left and right expressions
    Expr leftExpr = expr2.getLeftExpr();
    Expr rightExpr = expr2.getRightExpr();

    result = isSchema(leftExpr) & isSchema(rightExpr);

    return result;
  }

  //checks that the expr has the type 'power schema'
  protected boolean isSchema(Expr expr)
  {
    boolean result = true;

    Type type = (Type) expr.accept(this);
    Type elementType =  getBaseType(type);

    if (!(elementType instanceof SchemaType)) {
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
    SchemaType leftBaseType =
      (SchemaType) getBaseType(leftType);
    SchemaType rightBaseType =
      (SchemaType) getBaseType(rightType);

    result = signaturesCompatible(leftBaseType.getSignature(),
				  rightBaseType.getSignature());

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
	    leftPair.getName().toString();
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

  //decorate each name in a signature with a specified stroke
  protected SchemaType decorate(SchemaType schemaType, Stroke stroke)
  {
    SchemaType clonedSchemaType = (SchemaType) cloneType(schemaType);
    Signature signature = clonedSchemaType.getSignature();

    for (Iterator iter = signature.getNameTypePair().iterator();
	 iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      nameTypePair.getName().getStroke().add(stroke);
    }

    return clonedSchemaType;
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

  //replace all references to generic types by their actual counterparts
  //precondition: the "top-level" of the types are the same
  protected boolean unifyGenTypes(Type formal, Type actual)
  {
    boolean result = true;

    if (formal instanceof GenType) {
      GenType formalGen = (GenType) formal;
      unificationEnv_.add(formalGen.getName(), actual);
      result = true;
    }
    else if (formal instanceof PowerType && actual instanceof PowerType) {
      PowerType formalPower = (PowerType) formal;
      PowerType actualPower = (PowerType) actual;
      result = unifyGenTypes(formalPower.getType(), actualPower.getType());
    }
    else if (formal instanceof GivenType && actual instanceof GivenType) {
      result = true;
    }
    else if (formal instanceof SchemaType && actual instanceof SchemaType) {
      SchemaType formalSchema = (SchemaType) formal;
      SchemaType actualSchema = (SchemaType) actual;

      /*
      if (formalSchema.getSignature().getNameTypePair().size() ==
	  actualSchema.getSignature().getNameTypePair().size()) {
	
	//TODO: not sure what to do with schemas yet
      }
      */
      result = true;
    }
    else if (formal instanceof ProdType && actual instanceof ProdType) {

      ProdType formalProd = (ProdType) formal;
      ProdType actualProd = (ProdType) actual;

      if (formalProd.getType().size() == actualProd.getType().size()) {

	for (int i = 0; i < formalProd.getType().size(); i++) {
	  Type formalNext = (Type) formalProd.getType().get(i);
	  Type actualNext = (Type) actualProd.getType().get(i);
	  result = unifyGenTypes(formalNext, actualNext);
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

  protected Type replaceGenTypes(Type type)
  {
    Type result = unknownType();

    if (type instanceof GenType) {
      GenType genType = (GenType) type;
      result = unificationEnv_.getType(genType.getName());
    }
    else if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      Type replaced = replaceGenTypes(powerType.getType());
      result = factory_.createPowerType(replaced);
    }
    else if (type instanceof GivenType) {
      result = type;
    }
    else if (type instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) type;
      //TODO: ???
    }
    else if (type instanceof ProdType) {
      ProdType prodType = (ProdType) type;

      //the list of types for the new cross product
      List types = list();

      for (Iterator iter = prodType.getType().iterator(); iter.hasNext(); ) {
	Type next = (Type) iter.next();
	Type replaced = replaceGenTypes(next);
	types.add(replaced);
      }

      result = factory_.createProdType(types);
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

  //clone is used to do a recursive clone on a type
  protected Type cloneType(Type type)
  {
    CloningVisitor cloningVisitor = new CloningVisitor();
    return (Type) type.accept(cloningVisitor);
  }

  protected UnknownType unknownType()
  {
    return UnknownTypeImpl.create();
  }

  protected void exception(String message)
  {
    exception(-1, null, null, message);
  }

  protected void exception (int kind, Term term)
  {
    exception(kind, term, null, null);
  }

  protected void exception (int kind, Term term1, String message)
  {
    exception(kind, term1, null, message);
  }

  protected void exception (int kind, Term term1, Term term2)
  {
    exception(kind, term1, term2, null);
  }

  protected void exception (int kind, Term term1, Term term2, String message)
  {
    TypeException e =
      new TypeException(kind, term1, term2, message);
    exceptions_.add(e);
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
    System.err.println("EXCEPTION:\n\t " + e.toString());
  }

  protected void debug(String message)
  {
    if (DEBUG_) {
      System.err.println(message);
    }
  }
}
