package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.io.StringWriter;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.print.z.PrintUtils;

import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * A <code>TypeAnnotatingVisitor</code> visits an AST and adds type
 * annotations to the terms in this AST.  In this class, only some
 * visit methods return non-null objects:
 *
 * - all visit methods to Expr objects return the type (Type2) of the
 * expression
 *
 * - all visit methods to Decl objects return a list of NameTypePair
 * objects indicating the variables and their types declared in that
 * Decl.
 *
 * - the visit method for SchText return the signature of that schema
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
             ExprPredVisitor
{
  //a ZFactory for creating Z terms
  protected ZFactory factory_;

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv_;

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv_;

  //the TypeEnv for pending global declarations
  protected TypeEnv pending_;

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv_;

  //true if and only if the current SchText should add
  //its declarations as global
  protected boolean global_ = false;

  protected SectionManager manager_;

  protected boolean debug_ = false;

  public TypeAnnotatingVisitor(SectTypeEnv sectTypeEnv, SectionManager manager)
  {
    manager_ = manager;
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    sectTypeEnv_ = sectTypeEnv;
    typeEnv_ = new TypeEnv();
    pending_ = new TypeEnv();
    unificationEnv_ = new UnificationEnv();
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

    sectTypeEnv_.dump();
    return sectTypeEnv_;
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

    return sectTypeEnv_;
  }

  public Object visitParent(Parent parent)
  {
    sectTypeEnv_.addParent(parent.getWord());

    //get the types of the parent... this should be updated once the
    //session manager is finalised
    Term term = (Term) manager_.getInfo(parent.getWord(), ZSect.class);
    String section = sectTypeEnv_.getSection();
    term.accept(this);
    TypeChecker typechecker = new TypeChecker(manager_);
    //term.accept(typechecker);
    sectTypeEnv_.setSection(section);
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
      addTypeAnn(declName, powerType);

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
    addGenParamTypes(axPara.getDeclName());

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
      Type2 exprType = (Type2) expr.accept(this);

      PowerType varPowerType = factory_.createPowerType(variableType());
      Type unified = unificationEnv_.unify(varPowerType, exprType);

      if (unified != null) {
        ProdType prodType =
          factory_.createProdType(list(powerType(unified).getType(),
                                       givenType));
        PowerType powerType =
          factory_.createPowerType(prodType);
        nameTypePair = factory_.createNameTypePair(declName, powerType);
      }
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
    addGenParamTypes(conjPara.getDeclName());

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
      //pending_.enterScope();
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

    //now add the constrained declarations to the SectTypeEnv
    //sectTypeEnv_.add(pending_.getNameTypePair());

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
    Type2 exprType = (Type2) expr.accept(this);

    //get the type of this variable
    VariableType varType = variableType();
    TypeAnn typeAnn = factory_.createTypeAnn();
    varType.getDependent().add(typeAnn);

    PowerType powerType = factory_.createPowerType(varType);
    Type2 unified = unificationEnv_.unify(powerType, exprType);

    if (unified != null) {
      Type2 baseType = getBaseType(unified);
      Type thisType = addGenerics(baseType);
      typeAnn.setType(baseType);

      //get and visit the DeclNames
      List declNames = varDecl.getDeclName();
      for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
        DeclName declName = (DeclName) iter.next();
        addTypeAnn(declName, typeAnn);

        //add the name and its type to the list of NameTypePairs
        NameTypePair nameTypePair =
          factory_.createNameTypePair(declName, thisType);
        nameTypePairs.add(nameTypePair);
      }
    }

    return nameTypePairs;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    //the list of name type pairs in this ConstDecl
    //(this list will have only one element)
    List nameTypePairs = list();

    //get the DeclName
    DeclName declName = constDecl.getDeclName();

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    VariableType varType = variableType();
    TypeAnn typeAnn = factory_.createTypeAnn();
    varType.getDependent().add(typeAnn);

    Type2 unified = unificationEnv_.unify(varType, exprType);
    typeAnn.setType(unified);

    //if the type is unknown, don't use the subtype
    if (isUnknownType(unified)) {
      unknownType(unified).setUseBaseType(false);
    }

    //if there are parameters, add them to the generic type
    Type thisType = addGenerics(unified);

    //create the NameTypePair and add it to the list
    NameTypePair nameTypePair =
      factory_.createNameTypePair(declName, thisType);
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
    Type2 exprType = (Type2) expr.accept(this);

    VariableSignature varSig = variableSignature();
    SchemaType schemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(schemaType);

    Type2 unified = unificationEnv_.unify(powerType, exprType);

    if (unified != null) {
      for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        addTypeAnn(nameTypePair.getName(), unified);
      }
      nameTypePairs.addAll(schemaType.getSignature().getNameTypePair());
    }

    return nameTypePairs;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    RefName refName = refExpr.getRefName();
    Type refNameType = getType(refName);

    Type type = unknownType();
    List exprs = refExpr.getExpr();

    //get the parameters associated with this name and
    List params = list();
    if (refNameType instanceof GenericType) {
      GenericType genericType = (GenericType) refNameType;
      params = genericType.getName();
    }

    if (params.size() == exprs.size()) {

      //replace any references to generic types by the actual types in
      //the expression
      unificationEnv_.enterScope();

      Iterator exprIter = exprs.iterator();
      for (Iterator iter = params.iterator(); iter.hasNext(); ) {
        //get the next name and create a generic types
        DeclName declName = (DeclName) iter.next();

        //get the type of the next expression
        VariableType varType = variableType();
        PowerType powerType = factory_.createPowerType(varType);

        Expr expr = (Expr) exprIter.next();
        Type2 exprType = (Type2) expr.accept(this);
        Type2 unified = unificationEnv_.unify(powerType, exprType);

        if (unified != null) {
          Type2 replacementType = powerType(unified).getType();

          //add the type to the environment
          boolean uni =
            unificationEnv_.add(declName, (Type2) replacementType);
        }
      }
    }

    //replace all references to generic types with their
    //unified counterparts
    type = instantiate(refNameType);

    if (params.size() == exprs.size()) {
      unificationEnv_.exitScope();
    }

    //add the type annotation
    addTypeAnn(refExpr, type);

    Type2 result = null;
    if (type instanceof GenericType) {
      result = genericType(type).getOptionalType();
    }
    else {
      result = (Type2) refNameType;
    }

    return result;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    //get the expr and its type
    Expr expr = powerExpr.getExpr();
    Type2 innerType = (Type2) expr.accept(this);

    //the type of a PowerExpr is the set of sets of the
    //types inside the PowerExpr
    PowerType type = factory_.createPowerType(innerType);

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
    int position = 1;
    List exprs = prodExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); position++) {
      Expr expr = (Expr) iter.next();
      Type2 nestedType = (Type2) expr.accept(this);

      PowerType varPowerType = factory_.createPowerType(variableType());
      Type unified = unificationEnv_.unify(varPowerType, nestedType);

      if (unified != null) {
        types.add(powerType(unified).getType());
      }
    }

    if (types.size() == exprs.size()) {
      Type2 prodType = factory_.createProdType(types);
      type = factory_.createPowerType(prodType);
    }

    //add the type as an annotation
    addTypeAnn(prodExpr, type);

    return type;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    Type2 innerType = null;

    //get the inner expressions
    List exprs = setExpr.getExpr();

    //if the set is empty, then the inner type is variable
    if (exprs.size() == 0) {
      innerType = variableType();
    }
    //otherwise, find the inner type
    else {
      for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
        Expr expr = (Expr) iter.next();
        Type2 exprType = (Type2) expr.accept(this);

        //find a type of the inner expr. The typechecker will deal
        //with the condition that all types in the set are the same
        if (innerType == null) {
          innerType = exprType;
        }
        else {
          Type2 unified = unificationEnv_.unify(innerType, exprType);
          if (unified != null) {
            innerType = unified;
          }
        }
      }
    }

    //the type of a set expression is a power set of the
    //types inside the SetExpr
    Type2 type = factory_.createPowerType(innerType);

    //add the type as an annotion
    addTypeAnn(setExpr, type);

    return type;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    //the type of a NumExpr is the given type arithmos
    DeclName declName =
      factory_.createDeclName(ZString.ARITHMOS, list(), null);
    Type2 type = factory_.createGivenType(declName);

    //add the type as an annotation
    addTypeAnn(numExpr, type);

    return type;
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    //visit the SchText and add return the signature
    //from that as the signature for this expression
    boolean oldGlobal = global_;
    global_ = false;
    SchText schText = schExpr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = oldGlobal;

    SchemaType schemaType = factory_.createSchemaType(signature);
    PowerType type = factory_.createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(schExpr, type);

    return type;
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    //the type of the overall expression
    Type2 type = unknownType();

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
      types.add(unwrapType(nextType));
    }

    //if the expr is null, then use the signature to obtain the type
    if (expr == null) {

      //if the is only one element, then the type is a power set
      //of the type of that element
      if (types.size() == 1) {
        Type2 innerType = (Type2) types.get(0);
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
      Type2 exprType = (Type2) expr.accept(this);
      type = factory_.createPowerType(exprType);
    }

    //exit the variable scope
    typeEnv_.exitScope();

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
    ProdType type = factory_.createProdType(types);

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
    //TODO: should we try to unify here?
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
    boolean oldGlobal = global_;
    global_ = false;
    SchText schText = qnt1Expr.getSchText();
    Signature signature = (Signature) schText.accept(this);
    global_ = oldGlobal;

    Expr expr = qnt1Expr.getExpr();

    Type2 exprType = (Type2) expr.accept(this);

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(varSchemaType);

    Type2 unified = unificationEnv_.unify(powerType, exprType);

    //if the type of expr is a schema, then assign the type by
    //substracting schText's signature from expr's signature
    if (unified != null) {
      Signature qnt1ExprSignature =
        schemaHide(varSchemaType.getSignature(), signature);
      type = factory_.createSchemaType(qnt1ExprSignature);
    }

    //add the type annotation
    addTypeAnn(qnt1Expr, unified);

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

      //if there is more than one declaration, then the expr
      //is a tuple expr
      MuExpr transformedMuExpr = null;
      if (exprList.size() == 1) {
        Expr firstExpr = (Expr) exprList.get(0);
        transformedMuExpr = factory_.createMuExpr(schText, firstExpr);
      }
      else {
        TupleExpr tupleExpr = factory_.createTupleExpr(exprList);
        transformedMuExpr = factory_.createMuExpr(schText, tupleExpr);
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
    boolean oldGlobal = global_;
    global_ = false;
    schText.accept(this);
    global_ = oldGlobal;

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
    VariableSignature leftVarSig = variableSignature();
    SchemaType leftSchema = factory_.createSchemaType(leftVarSig);
    PowerType leftPower = factory_.createPowerType(leftSchema);

    VariableSignature rightVarSig = variableSignature();
    SchemaType rightSchema = factory_.createSchemaType(rightVarSig);
    PowerType rightPower = factory_.createPowerType(rightSchema);

    Type2 leftUnified = unificationEnv_.unify(leftPower, leftType);
    Type2 rightUnified = unificationEnv_.unify(rightPower, rightType);

    if (leftUnified != null && rightUnified != null) {

      Signature leftSig = schemaType(leftPower.getType()).getSignature();
      Signature rightSig = schemaType(rightPower.getType()).getSignature();

      if (signaturesCompatible(leftSig, rightSig)) {

        //the type is a power set of a schema that has the union of the
        //two signatures
        Signature signature = unionSignatures(leftSig, rightSig);
        SchemaType schemaType = factory_.createSchemaType(signature);
        type = factory_.createPowerType(schemaType);
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
    pred.accept(this);

    //get the type of the left and right expr
    Expr leftExpr = condExpr.getLeftExpr();
    Expr rightExpr = condExpr.getRightExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);
    Type2 rightType = (Type2) rightExpr.accept(this);

    Type2 unified = unificationEnv_.unify(leftType, rightType);

    if (unified != null) {
      type = unified;
    }

    //add the type annotation
    addTypeAnn(condExpr, type);

    return unified;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    //the type of this expression
    Type2 type = unknownType();

    //add the type annotation
    addTypeAnn(compExpr, type);

    throw new UnsupportedOperationException();
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    throw new UnsupportedOperationException();
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    Type2 type = unknownType();

    Expr expr = hideExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(varSchemaType);

    Type2 unified = unificationEnv_.unify(powerType, exprType);

    if (unified != null) {

      //hide the declarations
      SchemaType schemaType = (SchemaType) powerType(unified).getType();
      Signature signature = schemaHide(schemaType.getSignature(),
                                       hideExpr.getName());
      type = factory_.createSchemaType(signature);
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

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(varSchemaType);

    Type unified = unificationEnv_.unify(powerType, exprType);

    //the type of the expression is the same a preExpr, with all
    //primed and shrieked variables hidden
    if (unified != null) {

      SchemaType preSchemaType = schemaType(powerType(unified).getType());

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

    PowerType powerType = factory_.createPowerType(variableType());

    Type unified = unificationEnv_.unify(powerType, funcType);

    //if the left expression is a power set of a cross product, then
    //the type of the second component is the type of the whole
    //expression
    if (unified != null) {
      Type2 funcBaseType = powerType(unified).getType();
      if (isProdType(funcBaseType) &&
          prodType(funcBaseType).getType().size() == 2) {

        Type2 left = (Type2) prodType(funcBaseType).getType().get(0);
        unified = unificationEnv_.unify(left, argType);

        if (unified != null) {
          type = (Type2) prodType(funcBaseType).getType().get(1);
        }
      }
    }

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

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(varSchemaType);

    Type unified = unificationEnv_.unify(powerType, exprType);

    if (unified != null) {
      SchemaType schemaType = schemaType(powerType(unified).getType());

      //add the strokes to each name
      List nameTypePairs = schemaType.getSignature().getNameTypePair();
      for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        nameTypePair.getName().getStroke().addAll(thetaExpr.getStroke());
      }

      type = schemaType;
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

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(varSchemaType);

    Type unified = unificationEnv_.unify(powerType, exprType);

    //if the expr is a schema reference, decorate each name in the signature
    if (unified != null) {
      SchemaType schemaType = (SchemaType) powerType(unified).getType();
      SchemaType decoratedSchemaType =
        decorate(schemaType, decorExpr.getStroke());
      type = factory_.createPowerType(decoratedSchemaType);
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

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);
    PowerType powerType = factory_.createPowerType(varSchemaType);

    Type unified = unificationEnv_.unify(powerType, exprType);

    //if the expr is a schema reference, decorate each name in the signature
    if (unified != null) {
      SchemaType schemaType =
        (SchemaType) cloneType(powerType(unified).getType());
      List nameTypePairs = schemaType.getSignature().getNameTypePair();

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

      type = schemaType;
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

    VariableSignature varSig = variableSignature();
    SchemaType varSchemaType = factory_.createSchemaType(varSig);

    Type unified = unificationEnv_.unify(varSchemaType, exprType);

    //if expr is a binding, then get the type of the name
    if (unified != null) {
      SchemaType schemaType = schemaType(unified);
      RefName refName = bindSelExpr.getName();

      for (Iterator iter =
             schemaType.getSignature().getNameTypePair().iterator();
           iter.hasNext(); ) {
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
        factory_.createNameTypePair(declName, exprType);
      nameTypePairs.add(nameTypePair);
    }

    //create the type
    Signature signature = factory_.createSignature(nameTypePairs);
    type = factory_.createSchemaType(signature);

    //add the type annotation
    addTypeAnn(bindExpr, type);

    return type;
  }

  ///// predicates /////////

  /**
   * Exists1Pred, ExistsPred, and ForallPred instances are
   * visited as an instance of their super class QntPred.
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

  public Object visitMemPred(MemPred memPred)
  {
    //visit the left and right expressions
    Expr leftExpr = memPred.getLeftExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);

    Expr rightExpr = memPred.getRightExpr();
    Type2 rightType = (Type2) rightExpr.accept(this);

    PowerType powerType = factory_.createPowerType(leftType);

    Type unified = unificationEnv_.unify(powerType, rightType);

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

  //if there are generics in the current type env, return a new
  //GenericType with this Type2 as the type
  protected Type addGenerics(Type2 type)
  {
    Type result = null;

    if (typeEnv_.getParameters().size() > 0) {
      result =
        factory_.createGenericType(typeEnv_.getParameters(), type, null);
    }
    else {
      result = type;
    }

    return result;
  }

  //add generic types from a list of DeclNames to the TypeEnv
  protected void addGenParamTypes(List declNames)
  {
    typeEnv_.setParameters(declNames);

    //add each DeclName and its type
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();

      //we don't visit these DeclNames because given types
      //have a unique type inference rule
      GenParamType genParamType = factory_.createGenParamType(declName);
      PowerType powerType = factory_.createPowerType(genParamType);
      addTypeAnn(declName, powerType);

      //add the name and type to the TypeEnv
      typeEnv_.add(declName, powerType);
    }
  }

  //if this is a generic type, get the type without the parameters. If
  //not a generic type, return the type
  protected Type2 unwrapType(Type type)
  {
    Type2 result = null;

    if (type instanceof GenericType) {
      if (genericType(type).getOptionalType() != null) {
        result = genericType(type).getOptionalType();
      }
      else {
        result = genericType(type).getType();
      }
    }
    else {
      result = (Type2) type;
    }

    return result;
  }

  //gets the type of the expression represented by a name
  protected Type getType(Name name)
  {
    //get the type from the TypeEnv
    Type type = typeEnv_.getType(name);

    //if the TypeEnv did not know of this expression, then
    //ask the SectTypeEnv
    if (isUnknownType(type)) {
      Type sectTypeEnvType = sectTypeEnv_.getType(name);
      if (!isUnknownType(sectTypeEnvType)) {
        type = cloneType(sectTypeEnvType);
      }
    }

    //if not in either environments, return an unknown type with the
    //specified name
    if (isUnknownType(type)) {
      DeclName declName =
        factory_.createDeclName(name.getWord(), name.getStroke(), null);
      type = unknownType(declName, true);
    }

    return type;
  }

  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown.
   */
  public static Type2 getBaseType(Type2 type2)
  {
    Type2 result = unknownType();

    //if it's a PowerType, get the base type
    if (isPowerType(type2)) {
      PowerType powerType = (PowerType) type2;
      result = powerType.getType();
    }
    else if (isUnknownType(type2)) {
      result = type2;
    }

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

  protected Type instantiate(Type type)
  {
    Type result = unknownType();

    if (type instanceof Type2) {
      result = instantiate((Type2) type);
    }
    else {
      if (isGenericType(type)) {
        Type2 optionalType = instantiate(genericType(type).getType());
        genericType(type).setOptionalType(optionalType);
        result = type;
      }
    }

    return result;
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = unknownType();

    if (isGenParamType(type)) {
      GenParamType genParamType = (GenParamType) type;

      //try to get the type from the UnificationEnv
      Type unificationEnvType =
        unificationEnv_.getType(genParamType.getName());
      if (isUnknownType(unificationEnvType) &&
          typeEnv_.getParameters().contains(genParamType.getName())) {
        result = type;
      }
      else if (isUnknownType(unificationEnvType) &&
          unknownType(unificationEnvType).getName() == null) {
        result = variableType();
        unificationEnv_.add(genParamType.getName(), result);
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
        unificationEnv_.getType(variableType.getName());
      if (isUnknownType(unificationEnvType) &&
          unknownType(unificationEnvType).getName() == null) {
        result = variableType;
      }
      else if (unificationEnvType instanceof Type2) {
        result = (Type2) unificationEnvType;
      }
      else {
        // TODO: can this happen and what to do now?
        throw new CztException();
      }
    }
    else if (isPowerType(type)) {
      PowerType powerType = (PowerType) type;
      Type2 replaced = instantiate(powerType.getType());
      result = factory_.createPowerType(replaced);
    }
    else if (isGivenType(type)) {
      result = type;
    }
    else if (isSchemaType(type)) {
      SchemaType schemaType = (SchemaType) type;

      //the list of name type pairs for the new schema type
      List nameTypePairs = list();

      List formalNameTypePairs = schemaType.getSignature().getNameTypePair();
      for (Iterator iter = formalNameTypePairs.iterator(); iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        Type replaced = instantiate(nameTypePair.getType());
        NameTypePair newPair =
          factory_.createNameTypePair(nameTypePair.getName(), replaced);
        nameTypePairs.add(newPair);
      }

      Signature signature = factory_.createSignature(nameTypePairs);
      result = factory_.createSchemaType(signature);
    }
    else if (isProdType(type)) {
      ProdType prodType = (ProdType) type;

      //the list of types for the new cross product
      List types = list();

      for (Iterator iter = prodType.getType().iterator(); iter.hasNext(); ) {
        Type next = (Type) iter.next();
        Type replaced = instantiate(next);
        types.add(replaced);
      }

      result = factory_.createProdType(types);
    }

    return result;
  }

  protected static boolean isSchemaType(Object o)
  {
    return (o instanceof SchemaType);
  }

  protected static boolean isPowerType(Object o)
  {
    return (o instanceof PowerType);
  }

  protected static boolean isGivenType(Object o)
  {
    return (o instanceof GivenType);
  }

  protected static boolean isGenericType(Object o)
  {
    return (o instanceof GenericType);
  }

  protected static boolean isGenParamType(Object o)
  {
    return (o instanceof GenParamType);
  }

  protected static boolean isProdType(Object o)
  {
    return (o instanceof ProdType);
  }

  protected static boolean isUnknownType(Object o)
  {
    return (o instanceof UnknownType);
  }

  protected static boolean isVariableType(Object o)
  {
    return (o instanceof VariableType);
  }

  //non-safe typecast
  protected static SchemaType schemaType(Object o)
  {
    return (SchemaType) o;
  }

  //non-safe typecast
  protected static PowerType powerType(Object o)
  {
    return (PowerType) o;
  }

  //non-safe typecast
  protected static GivenType givenType(Object o)
  {
    return (GivenType) o;
  }

  //non-safe typecast
  protected static GenericType genericType(Object o)
  {
    return (GenericType) o;
  }

  //non-safe typecast
  protected static GenParamType genParamType(Object o)
  {
    return (GenParamType) o;
  }

  //non-safe typecast
  protected static ProdType prodType(Object o)
  {
    return (ProdType) o;
  }

  //non-safe typecast
  protected static UnknownType unknownType(Object o)
  {
    return (UnknownType) o;
  }

  //non-safe typecast
  protected static VariableType variableType(Object o)
  {
    return (VariableType) o;
  }

  //adds an annotation to a TermA
  protected void addAnns(TermA termA, Object ann)
  {
    if (ann != null) {
      termA.getAnns().add(ann);
    }
  }

  //add a type annotation, removing any existing type annotation
  protected void addTypeAnn(TermA termA, TypeAnn typeAnn)
  {
    TypeAnn existing = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (existing != null) {
      termA.getAnns().remove(existing);
    }

    termA.getAnns().add(typeAnn);
  }

  //adds a type annotation created from a type to
  //a TermA
  protected void addTypeAnn(TermA termA, Type type)
  {
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn == null) {
      typeAnn = factory_.createTypeAnn();
    }

    //if the type is null, add an UnknownType
    if (type != null) {
      typeAnn.setType(type);
    }
    else {
      typeAnn.setType(unknownType());
    }

    addAnns(termA, typeAnn);
  }

  //converts a Term to a string
  protected String format(Term term)
  {
    StringWriter writer = new StringWriter();
    PrintUtils.printUnicode(term, writer, manager_);
    return writer.toString();
  }

  //get the position of a TermA from its annotations
  protected String position(TermA termA)
  {
    String result = "Unknown location";

    for (Iterator iter = termA.getAnns().iterator(); iter.hasNext(); ) {
      Object next = iter.next();

      if (next instanceof LocAnn) {
        LocAnn locAnn = (LocAnn) next;
        result = "File: " + locAnn.getLoc() + "\n";
        result += "Position: " + locAnn.getLine() +
          ", " + locAnn.getCol() + "\n";
        break;
      }
    }

    return result;
  }

  //clone is used to do a recursive clone on a type
  protected Type cloneType(Type type)
  {
    CloningVisitor cloningVisitor = new CloningVisitor();
    return (Type) type.accept(cloningVisitor);
  }

  protected static VariableType variableType()
  {
    return VariableTypeImpl.create();
  }

  protected static VariableSignature variableSignature()
  {
    return VariableSignature.create();
  }

  protected static UnknownType unknownType()
  {
    return UnknownTypeImpl.create();
  }

  protected static UnknownType unknownType(DeclName declName,
                                           boolean useBaseType)
  {
    return UnknownTypeImpl.create(declName, useBaseType);
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
    if (debug_) {
      System.err.println(message);
    }
  }
}
