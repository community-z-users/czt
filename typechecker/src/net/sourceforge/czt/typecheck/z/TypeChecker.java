/* to do:
*. before going into type equation, change parent_ to the current Term
*. whenever a type equation throws an exception, should add a variable type
   to its type anns
*. name of any ZSect cannot be any of the prelude and toolkit sections!
*. change the search methods in TypeEnv and SectTypeEnv to search for
*  DeclName instead of String (done!)
*. integrate type environment with the type checker: PARTIALLY DONE
*. change the structure, maybe make typechecker a superclass of typechecker
   for z, oz and tcoz...
   so that common elements such as spec and read write file can be
   implemented in just 1 place
*/

package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Vector;
import java.io.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;

import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.util.transformer.z.Transformer;

import net.sourceforge.czt.typecheck.typeinference.z.*;

public class TypeChecker
  implements TermVisitor,
             TermAVisitor,
             SpecVisitor,
             ZSectVisitor,
             ParentVisitor,
             GivenParaVisitor,
             DeclNameVisitor,
             AxParaVisitor,
             ConstDeclVisitor,
             VarDeclVisitor,
             //InclDeclVisitor,
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
             NegExprVisitor
             //SectTypeEnvAnnVisitor
             //AndPredVisitor, ForallPredVisitor
             //ZVisitor
{
  private static String repository_ = "../toolkit";

  // used when current file uses a Z section that is not pre-defined
  // it stores the directory of current file
  private String curDir_;

  private ZFactory factory_;
  private XmlReader reader_;

  private TypeEnv typeEnv_;
  private SectTypeEnv sectTypeEnv_;

  // for storing the parent of the current term under checking
  private Term parent_;

  // for storing the name of the current section
  private String sectName_;

  // for syntax transformation of various Terms and TermAs
  private Transformer transformer_;

  // a list of type equations
  // should be solvable on a per-paragraph basis
  private Vector typeEqs_;

  public TypeChecker ()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    reader_ = new JaxbXmlReader();
    typeEnv_ = new TypeEnv();
    sectTypeEnv_ = new SectTypeEnv();
    curDir_ = new String();
    parent_ = null;
    sectName_ = null;
    transformer_ = new Transformer(factory_);
  }

  public Term checkFile(String fileName)
    throws Exception
  {
    File file = new java.io.File(fileName);
    return checkFile(file);
  }

  private Term checkFile(File file)
  {
    Term spec = (Term) reader_.read(file);
    Term result = (Term) spec.accept(this);
    String path = file.getParent();
    System.out.println("File path = " + path);
    curDir_ = path;
    System.out.println("curDir = " + curDir_);
    return result;
  }

  /**
   * Visits all children of a term.
   */
  public Object visitTerm(Term term)
  {
    try {
      return VisitorUtils.visitTerm(this, term, true);
    }
    catch (NullPointerException e) {
      return null;
    }
  }

  /**
   * Visits all children of a term and copies annotations.
   */
  public Object visitTermA(TermA oldTermA)
  {
    TermA newTermA = (TermA) visitTerm(oldTermA);
    if (newTermA != oldTermA) {
      newTermA.getAnns().addAll(oldTermA.getAnns());
    }
    return newTermA;
  }

  public Object visitSpec(Spec term)
  {
    List zsects = term.getSect();
    for (int i = 0; i < zsects.size(); i++) {
      Sect sect = (Sect) zsects.get(i);
      if (sect instanceof ZSect) {
        visitZSect((ZSect) sect);
      }
    }
    return term;
  }

  public Object visitZSect(ZSect term)
  {
    String name = term.getName();
    System.out.println("ZSect name is: " + name);
    sectName_ = new String(name);
    if (term instanceof TermA) {
      List list = term.getAnns();
      for (int i = 0; i < list.size(); i++) {
        Term sectAnn = (Term) list.get(i);
        if (sectAnn instanceof SectTypeEnvAnn) {
          sectTypeEnv_.checkAndAdd((SectTypeEnvAnn) sectAnn);
        }
      }
    }
    List parents = term.getParent();
    // add prelude if it is not one of the parent sections
    // only when current section is not prelude (!)
    if (! containsPrelude(parents)) {
      Parent prePare = factory_.createParent("prelude");
      parents.add(0, prePare);
    }
    // visit the parent sections of the current section
    Vector pareNames = new Vector();
    for (int i = 0; i < parents.size(); i++) {
      Parent pare = (Parent) parents.get(i);
      String curName = pare.getWord();
      if (! (sectName_.equals(curName) || pareNames.contains(curName))) {
        pareNames.add(curName);
        System.out.println("visiting parent: " + curName);
        pare.accept(this);
      }
      else {
        System.out.println("self or visited! " + curName);
      }
    }
    List paras = term.getPara();
    for (int i = 0; i < paras.size(); i++) {
      Para para = (Para) paras.get(i);
      // cannot use try-catch here
      System.out.println("para type = " + para.getClass().getName());
      para.accept(this);
    }
    return term;
  }

  // assumption: names in givenpara cannot contain stroke
  public Object visitGivenPara(GivenPara term)
  {
    Term tmpPare = parent_;
    System.out.println("visiting given para now!!!");
    List declNames = term.getDeclName();
    GivenType curGType = null;
    PowerType curPType = null;

    NameTypePair ntPair = null;
    NameSectTypeTriple nstTriple = null;

    GivenTypeEq gte = new GivenTypeEq(typeEnv_, term, this);
    try {
      // temp vector to store all decl names
      Vector tmpList = (Vector) gte.solve();
    }
    catch (TypeException e) {
      parent_ = tmpPare;
      System.out.println(e.toString());
      return term;
    }

    // type ann for the given para
    SchemaType schemaType = factory_.createSchemaType();
    Signature typeann = schemaType.getSignature();
    List ntPairs = typeann.getNameTypePair();
    DeclName temp = null;
    for (int i = 0; i < declNames.size(); i++) {
      parent_ = term;
      temp = (DeclName) declNames.get(i);
      // make type here
      curGType = factory_.createGivenType();
      curGType.setName(temp);

      curPType = factory_.createPowerType();
      curPType.setType(curGType);

      // add type info to DeclName
      TypeAnn ta = factory_.createTypeAnn(curPType);
      temp = (DeclName) addAnns(temp, ta);

      // add to type environments
      ntPair = factory_.createNameTypePair(temp, curPType);
      try {
        typeEnv_.addNameTypePair(ntPair);
      }
      catch (TypeException e) {
        parent_ = tmpPare;
        System.out.println(e.toString());
      }
      // add to sect environment
      nstTriple = factory_.createNameSectTypeTriple(temp, sectName_, curPType);
      try {
        sectTypeEnv_.addNameSectTypePair(nstTriple);
      }
      catch (TypeException e) {
        parent_ = tmpPare;
        System.out.println(e.toString());
      }
      // add type env annotation here
      ntPairs.add(ntPair);
    }
    schemaType.setSignature(typeann); // may not be necessary
    TypeAnn tAnn = factory_.createTypeAnn(schemaType);
    term = (GivenPara) addAnns(term, tAnn);
    parent_ = tmpPare;
    return term;
  }

  public Object visitDeclName(DeclName term)
  {
    // DeclName in GivenPara (GivenType) or AxPara (GenType)
    // cannot contain strokes
    if (parent_ instanceof GivenPara || parent_ instanceof AxPara) {
      try {
        List strokes = term.getStroke();
        if (strokes.size() > 0)  {
          throw new TypeException (ErrorKind.EXTRA_STROKE, term);
        }
      }
      catch (TypeException e) {
        System.out.println(e.toString());
        return null;
      }
    }
    return term;
  }

  public Object visitAxPara(AxPara term)
  {
    Term tmpPare = parent_;
    typeEnv_.enterScope();

    AxParaTypeEq apte = new AxParaTypeEq(typeEnv_, term, this);
    parent_ = term;
    try {
      apte.solve();
    }
    catch (TypeException e) {
      parent_ = tmpPare;
      e.printStackTrace();
      return term;
    }

    parent_ = tmpPare;
    typeEnv_.exitScope();
    return term;
  }

  /**
   * Tests whether the current section's parents contain
   * the prelude section.
   */
  private boolean containsPrelude(List parents)
  {
    boolean result = false;

    for (int i = 0; i < parents.size(); i++) {
      String name = ((Parent) parents.get(i)).getWord();
      if (name != null && name.equals("prelude")) {
        result = true;
        break;
      }
    }
    return result;
  }

  public Object visitParent(Parent term)
  {
    String name = term.getWord();
    System.out.println("parent: " + name);
    try {
      File curFile = findFile(term);
      return checkFile(curFile);
    }
    catch (TypeException e) {
      System.out.println(e.toString() + "\n" + "Source: " + name);
      return null;
    }
  }

  public Object visitSetExpr(SetExpr term)
  {
    SetExprTypeEq setq = new SetExprTypeEq(typeEnv_, term, this);
    try {
      term = (SetExpr) setq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  public Object visitSetCompExpr(SetCompExpr term)
  {
    SetCompExprTypeEq scetq = new SetCompExprTypeEq(typeEnv_, term, this);
    try {
      term = (SetCompExpr) scetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // need a syntactic transformation for schema text?
  // 13.2.6.14
  public Object visitSchText(SchText term)
  {
    SchTextTypeEq sttq = new SchTextTypeEq(typeEnv_, term, this);
    try {
      term = (SchText) sttq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  /**
   * Visits a ConstDecl.
   */
  public Object visitConstDecl(ConstDecl term)
  {
    Term tmpPare = parent_;
    VarDecl vdecl =
      (VarDecl) ((VarDecl) transformer_.visitConstDecl(term)).accept(this);
    return vdecl;
  }

  // 13.2.6.13
  public Object visitVarDecl(VarDecl term)
  {
    VarDeclTypeEq vdte = new VarDeclTypeEq(typeEnv_, term, this);
    try {
      term = (VarDecl) vdte.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.5
  public Object visitPowerExpr(PowerExpr term)
  {
    PowerExprTypeEq petq = new PowerExprTypeEq(typeEnv_, term, this);
    try {
      term = (PowerExpr) petq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.6
  public Object visitTupleExpr(TupleExpr term)
  {
    TupleExprTypeEq tetq = new TupleExprTypeEq(typeEnv_, term, this);
    try {
      term = (TupleExpr) tetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.7
  public Object visitTupleSelExpr(TupleSelExpr term)
  {
    TupleSelExprTypeEq tsetq = new TupleSelExprTypeEq(typeEnv_, term, this);
    try {
      term = (TupleSelExpr) tsetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.8
  public Object visitBindExpr(BindExpr term)
  {
    BindExprTypeEq betq = new BindExprTypeEq(typeEnv_, term, this);
    try {
      term = (BindExpr) betq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.9
  public Object visitThetaExpr(ThetaExpr term)
  {
    ThetaExprTypeEq tetq = new ThetaExprTypeEq(typeEnv_, term, this);
    try {
      term = (ThetaExpr) tetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.10
  public Object visitBindSelExpr(BindSelExpr term)
  {
    BindSelExprTypeEq bsetq = new BindSelExprTypeEq(typeEnv_, term, this);
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
    ApplExprTypeEq aetq = new ApplExprTypeEq(typeEnv_, term, this);
    try {
      term = (ApplExpr) aetq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.12
  public Object visitMuExpr(MuExpr term)
  {
    MuExprTypeEq metq = new MuExprTypeEq(typeEnv_, term, this);
    try {
      term = (MuExpr) metq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.14
  public Object visitSchExpr(SchExpr term)
  {
    SchExprTypeEq setq = new SchExprTypeEq(typeEnv_, term, this);
    try {
      term = (SchExpr) setq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

  // 13.2.6.15
  public Object visitNegExpr(NegExpr term)
  {
    NegExprTypeEq netq = new NegExprTypeEq(typeEnv_, term, this);
    try {
      term = (NegExpr) netq.solve();
    }
    catch (TypeException e) {
      e.printStackTrace();
    }
    return term;
  }

//------------------------ visit methods stop here---------------------------//
//---------------------------------------------------------------------------//

  /**
   * First find the file in default repository
   * if not found, find it in the current directory.
   */
  private File findFile(Parent term) throws TypeException
  {
    String name = term.getWord();
    File result = null;
    try {
      result = new File(repository_, name);
    }
    catch (NullPointerException e) {
      try {
        result = new File(curDir_, name);
      }
      catch (NullPointerException e1) {
        throw new TypeException(ErrorKind.NO_PARENT, term);
      }
    }
    return result;
  }

  // assumption: Id in DeclName is not used
  public static boolean unify(Type type1, Type type2)
  {
    boolean result = true;
    Class c1 = type1.getClass();
    Class c2 = type2.getClass();
    if ((c1.equals(c2) && type1 instanceof VariableType) || (! c1.equals(c2)))
      return false;
    if (type1 instanceof GenType || type1 instanceof GivenType) {
      String name1 = ((GenType) type1).getName().getWord();
      String name2 = ((GenType) type2).getName().getWord();
      if (! name1.equals(name2)) return false;
      return true;
    }
    else if (type1 instanceof PowerType) {
      Type t11 = ((PowerType) type1).getType();
      Type t21 = ((PowerType) type2).getType();
      return unify(t11, t21);
    }
    else if (type1 instanceof ProdType) {
      List t11 = ((ProdType) type1).getType();
      List t21 = ((ProdType) type2).getType();
      if (t11.size() != t21.size()) return false;
      for (int i = 0; i < t11.size(); i++) {
        Type t12 = (Type) t11.get(i);
        Type t22 = (Type) t21.get(i);
        if (! unify(t12, t22)) return false;
      }
      return true;
    }
    else if (type1 instanceof SchemaType) {
      List s1 = ((SchemaType) type1).getSignature().getNameTypePair();
      List s2 = ((SchemaType) type2).getSignature().getNameTypePair();
      if (s1.size() != s2.size()) return false;
      if (s1.size() == 0) return true;
      for (int i = 0; i < s1.size(); i++) {
        NameTypePair ntp1 = (NameTypePair) s1.get(i);
        if (! findInSignature(ntp1, s2)) return false;
      }
    }
    else if (type1 instanceof VariableType) {
      type1 = (Type) type2.create(type2.getChildren());
    }
    else if (type2 instanceof VariableType) {
      type2 = (Type) type1.create(type1.getChildren());
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
    if (unify(type, t1)) return true;
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
   *
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

  public Type getTypeFromAnns(TermA term)
  {
    List anns = term.getAnns();
    TypeAnn ta = null;
    boolean found = false;
    for (int i = 0; i < anns.size(); i++) {
      Object tmp = anns.get(i);
      if (tmp instanceof TypeAnn) {
        ta = (TypeAnn) tmp;
        found = true;
        break;
      }
    }
    if (found) {
      Type result = ta.getType();
      return result;
    }
    else {
      VariableType vt = new VariableType();
      return vt;
    }
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

  public TypeEnvInt getTypeEnv()
  {
    return typeEnv_;
  }

  /*
    public void setTypeEnv(TypeEnv te) {
    typeEnv = te;
    }
  */
}
