package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Vector;
import java.io.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.util.transformer.z.Transformer;

import net.sourceforge.czt.typecheck.typeinference.z.*;

public class TypeChecker
  implements SpecVisitor,
             ZSectVisitor,
             GivenParaVisitor,
             AxParaVisitor,
	     FreeParaVisitor,
	     FreetypeVisitor,
	     BranchVisitor,
             ConstDeclVisitor,
             VarDeclVisitor,
             InclDeclVisitor,
             SchTextVisitor,
             SetExprVisitor,
             SetCompExprVisitor,
             PowerExprVisitor,
             TupleExprVisitor,
             TupleSelExprVisitor,
             BindExprVisitor,
             ThetaExprVisitor,
             BindSelExprVisitor,
             ApplExprVisitor,
             MuExprVisitor,
             SchExprVisitor,
             NegExprVisitor,
	     CondExprVisitor
{
  private ZFactory factory_;

  //the environment recording a name, its type, and the section in
  //which it was declared
  private SectTypeEnv sectTypeEnv_;

  //the list of exceptions thrown by retrieving type info
  protected List exceptions_;

  //the factory for creating error messages
  protected ErrorFactory error_;

  //for storing the name of the current section
  private String sectName_;

  private SectionManager manager_;

  //the writer which to write messages and errors
  protected Writer writer_;

  protected final boolean DEBUG_ = false;

  public TypeChecker(SectionManager manager)
  {
    manager_ = manager;
    error_ = new ErrorFactoryEnglish(manager);
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    sectName_ = null;
    sectTypeEnv_ = null;
    exceptions_ = list();
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
	  String message = error_.redeclaredSection(zSect.getName());
	  exception(message);
	}
	else {
	  names.add(zSect.getName());
	}
      }

      sect.accept(this);
    }

    //print any exceptions
    for (Iterator iter = exceptions_.iterator(); iter.hasNext(); ) {
      Exception e = (Exception) iter.next();
      debug(e);
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
	String message = error_.redeclaredParent(parent, sectName_);
	exception(message);
      }
      else if (parent.getWord().equals(sectName_)) {
       	String message = error_.selfParent(sectName_);
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
	String message = error_.strokeInGiven(declName);
	exception(message);
      }
      else if (names.contains(declName.getWord())) {
	String message = error_.redeclaredGiven(declName);
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
	String message = error_.strokeInGen(declName);
	exception(message);
      }
      else if (names.contains(declName.getWord())) {
	String message = error_.redeclaredGen(declName);
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
	String message = error_.unknownType(expr);
	exception(message);
      }
      else if (! (type instanceof PowerType)) {
	String message = error_.nonSetInFreeType(expr, type);
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
	String message = error_.strokeInGen(declName);
	exception(message);
      }
      else if (names.contains(declName.getWord())) {
	String message = error_.redeclaredGen(declName);
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
      String message = error_.unknownType(expr);
      exception(message);
    }
    else if (! (type instanceof PowerType)) {
      String message = error_.nonSetInDecl(expr, type);
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
      String message = error_.nonSchExprInInclDecl(inclDecl);
      exception(message);
    }

    return null;
  }

  /////// expressions ///////
  public Object visitRefExpr(RefExpr refExpr)
  {
    RefName refName = refExpr.getRefName();

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
      String message = error_.unknownType(expr);
      exception(message);
    }
    else if (! (type instanceof PowerType)) {
      String message = error_.nonSetInPowerExpr(powerExpr, type);
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
	    error_.typeMismatchInSetExpr(expr, exprType, baseType);
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
      String message = error_.unknownType(expr);
      exception(message);
    }
    //if the type is not a cross product, report an error
    else if (! (exprType instanceof ProdType)) {
      String message =
	error_.nonProdTypeInTupleSelExpr(tupleSelExpr, exprType);
      exception(message);
    }
    else {
      //if the selection index is less than 1, or greater than the
      //the tuple length, report an error
      ProdType prodType = (ProdType) exprType;
      if (tupleSelExpr.getSelect().intValue() > prodType.getType().size() ||
	  tupleSelExpr.getSelect().intValue() < 1) {

	String message =
	  error_.indexErrorInTupleSelExpr(tupleSelExpr, prodType);
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
    if (!typesUnify(leftExprType, rightExprType)) {
      String message =
	error_.typeMismatchInCondExpr(condExpr, leftExprType, rightExprType);
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
	  error_.duplicateInBindExpr(bindExpr, nameExprPair.getName());
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
    
    return null;
  }

  // 13.2.6.10
  public Object visitBindSelExpr(BindSelExpr term)
  {
    BindSelExprTypeEq bsetq = new BindSelExprTypeEq(sectTypeEnv_, term, this);
    try {
      term = (BindSelExpr) bsetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.11
  public Object visitApplExpr(ApplExpr term)
  {
    ApplExprTypeEq aetq = new ApplExprTypeEq(sectTypeEnv_, term, this);
    try {
      term = (ApplExpr) aetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  //------------------------ visit methods stop here-----------------------//
  //-----------------------------------------------------------------------//

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

	  }
	}
      }
    }
  }

  public static boolean typesUnify(Type type1, Type type2)
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

  // sig is a List of NameTypePair
  public static boolean findInSignature (NameTypePair dn, List sig)
  {
    DeclName dn0 = dn.getName();
    Type type = dn.getType();
    NameTypePair ntp = findDeclNameInSignature(dn0, sig);
    if (ntp == null) return false;
    Type t1 = ntp.getType();
    if (typesUnify(type, t1)) return true;
    return false;
  }

  // assumption: any unique name can only appear once in a NameTypePair list!
  public static NameTypePair findDeclNameInSignature(DeclName dn, List sig)
  {
    String name = dn.getWord();
    List strokes = dn.getStroke();
    NameTypePair ntp = null;
    DeclName dn1 = null;
    List strokes1 = null;
    String name1 = null;
    for (int i = 0; i < sig.size(); i++) {
      ntp = (NameTypePair) sig.get(i);
      dn1 = ntp.getName();
      name1 = dn1.getWord();
      strokes1 = dn1.getStroke();
      if (name != null && name.equals(name1)) {
        if (strokesAgree(strokes, strokes1) && IdsAgree(dn, dn1))
          return ntp;
      }
    }
    return null;
  }

  /**
   * @param s1 a list of Stroke
   * @param s2 a list of Stroke
   */
  public static boolean strokesAgree(List s1, List s2)
  {
    if (s1.size() != s2.size()) return false;
    if (s1.size() == 0) return true;
    Class c1 = null;
    Class c2 = null;
    for (int i = 0; i < s1.size(); i++) {
      Stroke s11 = (Stroke) s1.get(i);
      Stroke s21 = (Stroke) s2.get(i);
      c1 = s11.getClass();
      c2 = s21.getClass();
      if (! c1.equals(c2)) return false;
      if (s11 instanceof NumStroke) {
        Integer i1 = ((NumStroke) s1).getNumber();
        Integer i2 = ((NumStroke) s2).getNumber();
        if (! i1.equals(i2)) return false;
      }
    }
    return true;
  }

  public static boolean IdsAgree(DeclName dn1, DeclName dn2)
  {
    String id1 = dn1.getId();
    String id2 = dn2.getId();
    if (id1 == null && id2 == null) return true;
    if (id1 != null && id2 != null && id1.equals(id2)) return true;
    return false;
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

  //converts a Term to a string
  protected String format(Term term)
  {
    StringWriter writer = new StringWriter();
    PrintUtils.printUnicode(term, writer, manager_);
    return writer.toString();
  }

  protected String formatType(Type type)
  {
    TypeFormatter formatter = new TypeFormatter();
    Expr expr = (Expr) type.accept(formatter);
    return format(expr);
  }

  protected void exception(String message)
  {
    exception(-1, null, null, message);
  }

  protected void exception(int kind, Term term)
  {
    exception(kind, term, null, null);
  }

  protected void exception(int kind, Term term1, String message)
  {
    exception(kind, term1, null, message);
  }

  protected void exception(int kind, Term term1, Term term2)
  {
    exception(kind, term1, term2, null);
  }

  protected void exception(int kind, Term term1, Term term2, String message)
  {
    TypeException e =
      new TypeException(kind, term1, term2, message);
    exceptions_.add(e);
    //debug(e);
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
}
