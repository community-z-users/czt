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
 * expression.
 *
 * - all visit methods to Decl objects return a list of NameTypePair
 * objects indicating the variables and their types.
 *
 * - the visit method for SchText return the signature of that schema.
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
             AndPredVisitor,
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

  protected SectionManager manager_;

  protected boolean debug_ = false;

  public TypeAnnotatingVisitor(SectTypeEnv sectTypeEnv, SectionManager manager)
  {
    manager_ = manager;
    factory_ = new net.sourceforge.czt.typecheck.util.typingenv.Factory();
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
      addAnn(sect, sectTypeEnv_.getSectTypeEnvAnn());
    }

    //sectTypeEnv_.dump();
    //unificationEnv_.dump();
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
    term.accept(typechecker);
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
    addSignatureAnn(givenPara, signature);

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
    SchText schText = axPara.getSchText();
    Signature signature = (Signature) visitGlobalSchText(schText);

    //add the SchText signature as an annotation to this paragraph
    addSignatureAnn(axPara, signature);

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
      freetype.accept(this);
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

      if (isUnknownType(exprType)) {
        VariableType vType = variableType();
        exprType = factory_.createPowerType(vType);
      }

      VariableType vType = variableType();
      PowerType vPowerType = factory_.createPowerType(vType);
      boolean unified = unificationEnv_.unify(vPowerType, exprType);

      if (unified) {
        ProdType prodType =
          factory_.createProdType(list(vPowerType.getType(),
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

    //if it is a Pred2 visit the predicate again
    if (pred instanceof Pred2) {
      pred.accept(this);
    }

    //the annotation for a conjecture paragraph is an empty signature
    Signature signature = factory_.createSignature();
    addSignatureAnn(conjPara, signature);

    //exit the variable scope
    typeEnv_.exitScope();

    return null;
  }

  public Object visitGlobalSchText(SchText schText)
  {
    //the list of Names declared in this schema text
    List nameTypePairs = list();

    //get and visit the list of declarations
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      nameTypePairs.addAll((List) decl.accept(this));
    }

    pending_.enterScope();
    pending_.add(nameTypePairs);

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      pred.accept(this);

      //if it is a Pred2 visit the predicate again
      if (pred instanceof Pred2) {
        pred.accept(this);
      }
    }

    //add the types from the pending environment into the the
    //SectTypeEnv
    for (Iterator iter = pending_.getNameTypePair().iterator();
         iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      Type type = addGenerics((Type2) pair.getType());
      sectTypeEnv_.add(pair.getName(), type);
    }

    //exit the pending scope
    pending_.exitScope();

    //the signature for this schema text
    Signature signature = factory_.createSignature(nameTypePairs);

    //add this as a type annotation
    addSignatureAnn(schText, signature);

    return signature;
  }

  public Object visitLocalSchText(SchText schText)
  {
    //the list of Names declared in this schema text
    List nameTypePairs = list();

    //get and visit the list of declarations
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      nameTypePairs.addAll((List) decl.accept(this));
    }

    typeEnv_.add(nameTypePairs);

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      pred.accept(this);

      //if it is a Pred2 visit the predicate again
      if (pred instanceof Pred2) {
        pred.accept(this);
      }
    }

    //the signature for this schema text
    Signature signature = factory_.createSignature(nameTypePairs);

    //add this as a type annotation
    addSignatureAnn(schText, signature);

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
    VariableType vType = variableType();
    PowerType powerType = factory_.createPowerType(vType);

    boolean unified = unificationEnv_.unify(powerType, exprType);
    if (unified) {
      Type2 baseType = powerType.getType();

      //get and visit the DeclNames
      List declNames = varDecl.getDeclName();
      for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
        DeclName declName = (DeclName) iter.next();

        //add the name and its type to the list of NameTypePairs
        NameTypePair nameTypePair =
          factory_.createNameTypePair(declName, baseType);
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

    debug("visiting ConstDecl " + declName);

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    //if the type is unknown, don't use the subtype
    if (isUnknownType(exprType)) {
      unknownType(exprType).setUseBaseType(false);
    }

    //create the NameTypePair and add it to the list
    NameTypePair nameTypePair =
      factory_.createNameTypePair(declName, exprType);
    nameTypePairs.add(nameTypePair);

    return nameTypePairs;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    debug("visiting InclDecl" + format(inclDecl.getExpr()));

    //the list of name type pairs in this InclDecl
    List nameTypePairs = list();

    //get the expression
    Expr expr = inclDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    if (unified) {
      for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
        NameTypePair nameTypePair = (NameTypePair) iter.next();
        addTypeAnn(nameTypePair.getName(), powerType);
      }
      nameTypePairs.addAll(vSchemaType.getSignature().getNameTypePair());
    }

    return nameTypePairs;
  }
  public Object visitRefExpr(RefExpr refExpr)
  {
    RefName refName = refExpr.getRefName();
    Type type = getType(refName);

    TypeAnn typeAnn = (TypeAnn) refExpr.getAnn(TypeAnn.class);
    if (typeAnn != null) {
      type = typeAnn.getType();
    }

    List exprs = refExpr.getExpr();

    //if it is a generic type, we must instantiate the optional type
    if (isGenericType(type)) {

      GenericType genericType = (GenericType) type;

      //if the instantiation is implicit
      if (exprs.size() == 0) {

        List instantiations = list();
        unificationEnv_.enterScope();

        if (typeAnn == null) {
          for (Iterator iter = genericType.getName().iterator();
               iter.hasNext(); ) {
            //get the next name and create a generic types
            DeclName declName = (DeclName) iter.next();

            if (!unificationEnv_.contains(declName)) {
              //add a variable type
              VariableType vType = variableType();
              unificationEnv_.addGenName(declName, vType);
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

        unificationEnv_.exitScope();
      }
      //if the instantiation is explicit
      else {

        if (genericType.getName().size() == exprs.size()) {

          unificationEnv_.enterScope();

          if (typeAnn == null) {
            Iterator exprIter = exprs.iterator();
            for (Iterator iter = genericType.getName().iterator();
                 iter.hasNext(); ) {

              //get the next name and create a generic types
              DeclName declName = (DeclName) iter.next();

              //get the type of the next expression
              VariableType vType = variableType();
              PowerType powerType = factory_.createPowerType(vType);

              Expr expr = (Expr) exprIter.next();
              Type2 exprType = (Type2) expr.accept(this);
              boolean unified = unificationEnv_.unify(powerType, exprType);

              if (unified) {
                Type2 replacementType = powerType.getType();

                //add the type to the environment
                unificationEnv_.addGenName(declName, (Type2) replacementType);
              }
            }
          }

          instantiate(genericType);

          unificationEnv_.exitScope();
        }
      }
    }

    if (type instanceof UnknownType) {
      System.err.println(refName.getWord() + " : " + type);
    }

    //add the type annotation
    addTypeAnn(refExpr, type);

    Type2 result = unwrapType(type);
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

      VariableType vType = variableType();
      PowerType vPowerType = factory_.createPowerType(vType);
      boolean unified = unificationEnv_.unify(vPowerType, nestedType);

      if (unified) {
        types.add(vPowerType.getType());
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
    //the type of a set expression is a power set of the
    //types inside the SetExpr
    Type2 innerType = variableType();
    Type2 type = getTypeFromAnns(setExpr);
    if (isUnknownType(type)) {
      type = factory_.createPowerType(innerType);
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

      unificationEnv_.unify(innerType, exprType);
    }

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
    SchText schText = schExpr.getSchText();
    Signature signature = (Signature) visitLocalSchText(schText);

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
    SchText schText = setCompExpr.getSchText();
    Signature signature = (Signature) visitLocalSchText(schText);

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
    //TODO: should we try to unify here... if so, how long should the
    //ProdType be?
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
    Signature signature = (Signature) visitLocalSchText(schText);

    Expr expr = qnt1Expr.getExpr();

    Type2 exprType = (Type2) expr.accept(this);

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    //if the type of expr is a schema, then assign the type by
    //substracting schText's signature from expr's signature
    if (unified) {
      Signature qnt1ExprSignature =
        schemaHide(vSchemaType.getSignature(), signature);
      type = factory_.createSchemaType(qnt1ExprSignature);
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
    Signature signature = (Signature) visitLocalSchText(schText);

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

      charTuple = factory_.createProdType(charTupleList);
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
        factory_.createProdType(list(charTuple, exprType));
      type = factory_.createPowerType(prodType);
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
    visitLocalSchText(schText);

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
    VariableSignature leftVSig = variableSignature();
    SchemaType leftSchema = factory_.createSchemaType(leftVSig);
    PowerType leftPower = factory_.createPowerType(leftSchema);

    VariableSignature rightVSig = variableSignature();
    SchemaType rightSchema = factory_.createSchemaType(rightVSig);
    PowerType rightPower = factory_.createPowerType(rightSchema);

    boolean leftUnified = unificationEnv_.unify(leftPower, leftType);
    boolean rightUnified = unificationEnv_.unify(rightPower, rightType);

    if (leftUnified && rightUnified) {

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
    else {
      System.err.println("HERE");
      System.exit(0);
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

    //if it is a Pred2 visit the predicate again
    if (pred instanceof Pred2) {
      pred.accept(this);
    }

    //get the type of the left and right expr
    Expr leftExpr = condExpr.getLeftExpr();
    Expr rightExpr = condExpr.getRightExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);
    Type2 rightType = (Type2) rightExpr.accept(this);

    boolean unified = unificationEnv_.unify(leftType, rightType);

    if (unified) {
      type = leftType;
    }

    //add the type annotation
    addTypeAnn(condExpr, leftType);

    return type;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    //the type of this expression
    Signature signature = variableSignature();
    SchemaType schemaType = factory_.createSchemaType(signature);
    Type2 type = factory_.createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(compExpr, type);

    return type;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    //the type of this expression
    Signature signature = variableSignature();
    SchemaType schemaType = factory_.createSchemaType(signature);
    Type2 type = factory_.createPowerType(schemaType);

    //add the type annotation
    addTypeAnn(pipeExpr, type);

    return type;
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    Type2 type = unknownType();

    Expr expr = hideExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    if (unified) {
      //hide the declarations
      SchemaType schemaType = (SchemaType) powerType.getType();
      Signature signature = schemaHide(schemaType.getSignature(),
                                       hideExpr.getName());
      SchemaType hideSchemaType = factory_.createSchemaType(signature);
      type = factory_.createPowerType(hideSchemaType);
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

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    //the type of the expression is the same a preExpr, with all
    //primed and shrieked variables hidden
    if (unified) {

      SchemaType preSchemaType = schemaType(powerType.getType());
      List oldPairs = preSchemaType.getSignature().getNameTypePair();

      NextStroke nextStroke = factory_.createNextStroke();
      OutStroke outStroke = factory_.createOutStroke();

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

      Signature signature = factory_.createSignature(newPairs);
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

    VariableType vType = variableType();
    PowerType powerType = factory_.createPowerType(vType);

    unificationEnv_.enterScope();
    boolean unified = unificationEnv_.unify(powerType, funcType);

    //if the left expression is a power set of a cross product, then
    //the type of the second component is the type of the whole
    //expression
    if (unified) {
      Type2 funcBaseType = powerType.getType();
      if (isProdType(funcBaseType) &&
          prodType(funcBaseType).getType().size() == 2) {

        Type2 domType = (Type2) prodType(funcBaseType).getType().get(0);

        boolean unifiedInner = unificationEnv_.unify(domType, argType);

        if (unifiedInner) {
          Type2 ranType = (Type2) prodType(funcBaseType).getType().get(1);
          type = instantiate(ranType);
          prodType(funcBaseType).getType().set(1, type);
        }
      }
    }

    unificationEnv_.exitScope();

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

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    if (unified) {
      SchemaType schemaType = schemaType(powerType.getType());

      //create a new SchemaType with each name decorated
      type = decorate(schemaType, thetaExpr.getStroke());
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

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    //if the expr is a schema reference, decorate each name in the signature
    if (unified) {
      SchemaType schemaType = (SchemaType) powerType.getType();
      SchemaType decoratedSchemaType =
        decorate(schemaType, list(decorExpr.getStroke()));
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

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);
    PowerType powerType = factory_.createPowerType(vSchemaType);

    boolean unified = unificationEnv_.unify(powerType, exprType);

    //if the expr is a schema reference, rename all rename pairs
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
              factory_.createNameTypePair(newName, newType);
            newPairs.add(newPair);
            addExisting = false;
          }
        }

        //if this name was not renamed, then add the existing pair
        if (addExisting) {
          newPairs.add(existingPair);
        }
      }

      Signature newSignature = factory_.createSignature(newPairs);
      SchemaType newSchemaType = factory_.createSchemaType(newSignature);
      type = factory_.createPowerType(newSchemaType);
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

    VariableSignature vSig = variableSignature();
    SchemaType vSchemaType = factory_.createSchemaType(vSig);

    boolean unified = unificationEnv_.unify(vSchemaType, exprType);

    //if expr is a binding, then get the type of the name
    if (unified) {
      SchemaType schemaType = schemaType(vSchemaType);
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
    SchText schText = qntPred.getSchText();
    visitLocalSchText(schText);

    //visit the Pred
    Pred pred = qntPred.getPred();
    pred.accept(this);

    //if it is a Pred2 visit the predicate again
    if (pred instanceof Pred2) {
      pred.accept(this);
    }

    //exit the variable scope
    typeEnv_.exitScope();

    return null;
  }

  /**
   * IffPred, ImpliesPred, and OrPred instances are
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
    //visit the left and right preds
    Pred leftPred = andPred.getLeftPred();
    leftPred.accept(this);

    Pred rightPred = andPred.getRightPred();
    rightPred.accept(this);

    //if this is a chain relation, unify the RHS of the left pred
    //with the LHS of the right predicate
    if (Op.Chain.equals(andPred.getOp())) {
      //MemPred leftMemPred = (MemPred) leftPred;
      //MemPred rightMemPred = (MemPred) rightPred;

      Type2 rhsLeft = getRightType(leftPred);
      Type2 lhsRight = getLeftType(rightPred);

      boolean unified = unificationEnv_.unify(rhsLeft, lhsRight);
    }

    return null;
  }

  protected Type2 getLeftType(Pred pred)
  {
    MemPred memPred = (MemPred) pred;
    List types = getLeftRightType(memPred);
    Type2 result = (Type2) types.get(0);
    return result;
  }

  protected Type2 getRightType(Pred pred)
  {
    Type2 result = null;

    if (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      List types = getLeftRightType(memPred);
      result = (Type2) types.get(1);
    }
    else if (pred instanceof AndPred) {
      AndPred andPred = (AndPred) pred;
      MemPred memPred = (MemPred) andPred.getRightPred();
      result = getRightType(memPred);
    }

    return result;
  }

  protected List getLeftRightType(MemPred memPred)
  {
    List result = list();

    Expr leftExpr = memPred.getLeftExpr();
    Expr rightExpr = memPred.getRightExpr();

    //if this pred is an equality
    boolean mixfix = memPred.getMixfix().booleanValue();
    if (mixfix && rightExpr instanceof SetExpr) {
      result.add(getTypeFromAnns(leftExpr));
      result.add(getBaseType(getTypeFromAnns(rightExpr)));
    }
    //if this is a membership
    else if (!mixfix) {
      result.add(getTypeFromAnns(leftExpr));
      result.add(getTypeFromAnns(rightExpr));
    }
    //if this is a relation
    else {
      if (leftExpr instanceof TupleExpr) {
        TupleExpr tupleExpr = (TupleExpr) leftExpr;
        result.add(getTypeFromAnns((Expr) tupleExpr.getExpr().get(0)));
        result.add(getTypeFromAnns((Expr) tupleExpr.getExpr().get(1)));
      }
      else {
        result.add(getTypeFromAnns(leftExpr));
      }
    }

    return result;
  }

  public Object visitMemPred(MemPred memPred)
  {
    //visit the left and right expressions
    Expr leftExpr = memPred.getLeftExpr();
    Type2 leftType = (Type2) leftExpr.accept(this);

    Expr rightExpr = memPred.getRightExpr();
    Type2 rightType = (Type2) rightExpr.accept(this);

    //unify the left and right side of the membership predicate
    PowerType powerType = factory_.createPowerType(leftType);

    unificationEnv_.unify(powerType, rightType);

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

      //add the name and type to the TypeEnv
      typeEnv_.add(declName, powerType);
    }
  }

  //if this is a generic type, get the type without the parameters. If
  //not a generic type, return the type
  protected static Type2 unwrapType(Type type)
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

    //if the type environment did not know of this expression.
    //then ask the pending env
    if (isUnknownType(type)) {
      type = pending_.getType(name);
    }

    //if the pending environment did not know of this expression,
    //then ask the SectTypeEnv
    if (isUnknownType(type)) {
      Type sectTypeEnvType = sectTypeEnv_.getType(name);
      if (!isUnknownType(sectTypeEnvType)) {
        type = cloneType(sectTypeEnvType);
      }
    }

    //if not in either environments, or does not start with a
    //delta or xi, return a variable type with the specified name
    if (isUnknownType(type)) {
      if (!name.getWord().startsWith(ZString.DELTA) &&
          !name.getWord().startsWith(ZString.XI)) {

        DeclName declName =
          factory_.createDeclName(name.getWord(), name.getStroke(), null);
        VariableType vType = variableType();
        vType.setName(declName);
        type = vType;

        //add an UndeclaredAnn
        UndeclaredAnn ann = new UndeclaredAnn();
        name.getAnns().add(ann);
      }
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
        factory_.createDeclName(oldName.getWord(), strokes, null);
      NameTypePair newPair =
        factory_.createNameTypePair(newName, oldPair.getType());
      nameTypePairs.add(newPair);
    }

    Signature newSignature = factory_.createSignature(nameTypePairs);
    SchemaType result = factory_.createSchemaType(newSignature);

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

    Signature result = factory_.createSignature(nameTypePairs);
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
      Type unificationEnvType =  unificationEnv_.getType(genName);

      //if this type's reference is in the parameters
      if (containsDoubleEquals(typeEnv_.getParameters(), genName)) {
        result = type;
      }
      else if (isUnknownType(unificationEnvType) &&
               unknownType(unificationEnvType).getName() == null) {
        VariableType vType = variableType();
        result = vType;
        unificationEnv_.addGenName(genName, result);
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

  protected static boolean isVariableSignature(Object o)
  {
    return (o instanceof VariableSignature);
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

  //non-safe typecast
  protected static VariableSignature variableSignature(Object o)
  {
    return (VariableSignature) o;
  }

  //adds an annotation to a TermA
  protected void addAnn(TermA termA, Object ann)
  {
    if (ann != null) {
      termA.getAnns().add(ann);
    }
  }

  //adds a type annotation created from a type to
  //a TermA
  protected void addTypeAnn(TermA termA, Type type)
  {
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn == null) {
      typeAnn = factory_.createTypeAnn(type);
      termA.getAnns().add(typeAnn);
    }
    else {
      typeAnn.setType(type);
    }
  }

  //adds a signature annotation create from a signature to a TermA
  protected void addSignatureAnn(TermA termA, Signature signature)
  {
    SignatureAnn signatureAnn =
      (SignatureAnn) termA.getAnn(SignatureAnn.class);

    if (signatureAnn == null) {
      signatureAnn = factory_.createSignatureAnn(signature);
      termA.getAnns().add(signatureAnn);
    }
    else {
      signatureAnn.setSignature(signature);
    }
  }

  protected void removeTypeAnn(TermA termA)
  {
    TypeAnn existing = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (existing != null) {
      termA.getAnns().remove(existing);
    }
  }

  protected TypeAnn getTypeAnn(TermA termA)
  {
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn == null) {
      typeAnn = factory_.createTypeAnn();
      addAnn(termA, typeAnn);
    }

    return typeAnn;
  }

  protected Type2 getTypeFromAnns(TermA termA)
  {
    Type result = unknownType();
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);
    if (typeAnn != null) {
      result = typeAnn.getType();
    }
    return unwrapType(result);
  }

  //returns true if and only if 'list' contains a reference to 'o'
  protected boolean containsDoubleEquals(List list, Object o)
  {
    boolean result = false;

    for (Iterator iter = list.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next == o) {
        result = true;
        break;
      }
    }

    return result;
  }

  //converts a Term to a string
  protected String format(Term term)
  {
    try {
      StringWriter writer = new StringWriter();
      PrintUtils.printUnicode(term, writer, manager_);
      return writer.toString();
    }
    catch (Exception e) {
      return "Cannot print";
    }
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

  protected List list(List list)
  {
    List result = new ArrayList(list);
    return result;
  }

  protected void debug(String message)
  {
    if (debug_) {
      System.err.println(message);
    }
  }
}
