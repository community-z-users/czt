package net.sourceforge.czt.typecheck.util.transformer.z;

import java.util.List;
import java.util.Vector;
import java.io.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;

import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

public class Transformer
  implements TermVisitor, TermAVisitor, SpecVisitor, ZSectVisitor,
             FreeParaVisitor, FreetypeVisitor,
             ExistsPredVisitor, IffPredVisitor, ImpliesPredVisitor,
             OrPredVisitor, ExprPredVisitor,
             LetExprVisitor, IffExprVisitor, ImpliesExprVisitor,
             OrExprVisitor, CondExprVisitor,
             ProjExprVisitor, ProdExprVisitor,
             ConstDeclVisitor
{
  private ZFactory factory_;
  private XmlReader reader_;
  //private Term spec;

  public Transformer()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    reader_ = new JaxbXmlReader();
  }

  public Transformer(ZFactory fa)
  {
    factory_ = fa; //new net.sourceforge.czt.z.impl.ZFactoryImpl();
    reader_ = new JaxbXmlReader();
  }

  /*
    public Transformer(String name) {
    this.Transformer();
    try {
    File file = new java.io.File(fileName);
    spec = (Term) reader_.read(file);
    } catch (Exception e) {
    e.printStackTrace();
    }
    }
    public Transoformer(File file) {
    this.Transformer();
    spec = (Term) reader_.read(file);
    }
  */

  public Term transformFile(File file)
  {
    Term spec = (Term) reader_.read(file);
    Term result = (Term) spec.accept(this);
    return result;
  }

  /**
   * Visit all children of a term.
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
   * Visit all children of a term and copy annotations.
   */
  public Object visitTermA(TermA oldTermA)
  {
    TermA newTermA = (TermA) visitTerm(oldTermA);
    if (newTermA != oldTermA) {
      newTermA.getAnns().addAll(oldTermA.getAnns());
    }
    return newTermA;
  }

  /**
   * Visit a spec by visiting all its Z Sections.
   */
  public Object visitSpec(Spec term)
  {
    List zsects = term.getSect();
    for (int i = 0; i < zsects.size(); i++) {
      Sect sect = (Sect) zsects.get(i);
      if (sect instanceof ZSect) {
        ((ZSect) sect).accept(this);
      }
    }
    return term;
  }

  /**
   * If prelude is not in the parent of the sect, add it.
   */
  public Object visitZSect(ZSect term)
  {
    List parents = term.getParent();
    Vector names = new Vector();
    boolean foundPrelude = false;
    String cur = null;
    for (int i = 0; i < parents.size(); i++) {
      cur = ((Parent) parents.get(i)).getWord();
      if (cur.equals("prelude")) {
        foundPrelude = true;
        break;
      }
    }
    if (! foundPrelude) {
      Parent par = factory_.createParent();
      par.setWord("prelude");
      parents.add(0, par);
    }
    return term;
  }

  /**
   * Syntactically transform a free type para.
   * Puts elements in front of injections.
   */
  public Object visitFreePara(FreePara term)
  {
    List freetypes = term.getFreetype();
    for (int i = 0; i < freetypes.size(); i++) {
      Freetype ft = (Freetype) freetypes.get(i);
      ft.accept(this);
    }
    return term;
  }

  public Object visitFreetype(Freetype term)
  {
    List branches = term.getBranch();
    List elements = new Vector();
    List injections = new Vector();
    Branch br = null;
    for (int i = 0; i < branches.size(); i++) {
      br = (Branch) branches.get(i);
      Expr expr = br.getExpr();
      if (expr == null) elements.add(br);
      else injections.add(br);
    }
    branches.clear();
    branches.addAll(elements);
    branches.addAll(injections);
    return term;
  }

  /**
   * Transforms an ExistsPred into a ForallPred.
   */
  public Object visitExistsPred(ExistsPred term)
  {
    SchText schtxt = (SchText) term.getSchText().accept(this);
    Pred pred = (Pred) term.getPred().accept(this);
    NegPred negP = factory_.createNegPred(pred);
    ForallPred faP = factory_.createForallPred(schtxt, negP);
    NegPred result = factory_.createNegPred(faP);
    return result;
  }

  /**
   * Transforms an IffPred into an AndPred.
   */
  public Object visitIffPred(IffPred term)
  {
    Pred left = (Pred) term.getLeftPred().accept(this);
    Pred right = (Pred) term.getRightPred().accept(this);
    ImpliesPred im1 = factory_.createImpliesPred(left, right);
    ImpliesPred im2 = factory_.createImpliesPred(right, left);
    AndPred result = factory_.createAndPred(im1, im2, Op.And);
    return result;
  }

  /**
   * Transforms an ImpliesPred into an OrPred.
   */
  public Object visitImpliesPred(ImpliesPred term)
  {
    Pred left = (Pred) term.getLeftPred().accept(this);
    Pred right = (Pred) term.getRightPred().accept(this);
    NegPred neg = factory_.createNegPred(left);
    OrPred result = factory_.createOrPred(neg, right);
    return result;
  }

  /**
   * Transforms an OrPred into an AndPred.
   */
  public Object visitOrPred(OrPred term)
  {
    Pred left = (Pred) term.getLeftPred().accept(this);
    Pred right = (Pred) term.getRightPred().accept(this);
    NegPred neg1 = factory_.createNegPred(left);
    NegPred neg2 = factory_.createNegPred(right);
    AndPred and = factory_.createAndPred(neg1, neg2, Op.And);
    NegPred result = factory_.createNegPred(and);
    return result;
  }

  /**
   * Transforms an ExprPred into a MemPred.
   */
  public Object visitExprPred(ExprPred term)
  {
    SchExpr expr = (SchExpr) term.getExpr().accept(this);
    Vector pairs = new Vector();
    SchText schtxt = expr.getSchText();
    List decls = schtxt.getDecl();
    Decl de = null;
    for (int i = 0; i < decls.size(); i++) {
      de = (Decl) decls.get(i);
      if (de instanceof VarDecl) {
        Vector tmp = addNameExprPair((VarDecl) de);
        pairs.addAll(tmp);
      }
    }
    BindExpr be = factory_.createBindExpr(pairs);
    MemPred result = factory_.createMemPred(expr, be, new Boolean(false));
    return result;
  }

  private Vector addNameExprPair(VarDecl de)
  {
    Vector result = new Vector();
    List names = ((VarDecl) de).getDeclName();
    Expr expr = ((VarDecl) de).getExpr();
    for (int i = 0; i < names.size(); i++) {
      DeclName dn = (DeclName) names.get(i);
      NameExprPair pair = factory_.createNameExprPair(dn, expr);
      result.add(pair);
    }
    return result;
  }

  /**
   * Transforms a let expr into a definite (\mu) expr.
   */
  public Object visitLetExpr(LetExpr term)
  {
    // transform the schema text part
    SchText schtxt = (SchText) term.getSchText().accept(this);
    // transform the expression part
    Expr expr = (Expr) term.getExpr().accept(this);
    MuExpr mu = factory_.createMuExpr(schtxt, expr);
    return mu;
  }

  /**
   * Transforms a schema equiv expr into a schema conjunction
   * of schema implications.
   */
  public Object visitIffExpr(IffExpr term)
  {
    // transform the left expr
    Expr left = (Expr) term.getLeftExpr().accept(this);
    // transform the right expr
    Expr right = (Expr) term.getRightExpr().accept(this);
    ImpliesExpr leftImplies = factory_.createImpliesExpr(left, right);
    ImpliesExpr rightImplies = factory_.createImpliesExpr(right, left);
    AndExpr andExpr = factory_.createAndExpr(leftImplies, rightImplies);
    return andExpr;
  }

  /**
   * Transforms a schema implication expr into a schema disjunction expr.
   */
  public Object visitImpliesExpr(ImpliesExpr term)
  {
    // transform the left expr
    Expr left = (Expr) term.getLeftExpr().accept(this);
    // transform the right expr
    Expr right = (Expr) term.getRightExpr().accept(this);
    NegExpr neg = factory_.createNegExpr(left);
    OrExpr orExpr = factory_.createOrExpr(neg, right);
    return orExpr;
  }

  /**
   * Transforms a schema disjunction into a schema negation.
   */
  public Object visitOrExpr (OrExpr term)
  {
    // transform the left expr
    Expr left = (Expr) term.getLeftExpr().accept(this);
    // transform the right expr
    Expr right = (Expr) term.getRightExpr().accept(this);
    NegExpr leftNeg = factory_.createNegExpr(left);
    NegExpr rightNeg = factory_.createNegExpr(right);
    AndExpr andExpr = factory_.createAndExpr(leftNeg, rightNeg);
    NegExpr result = factory_.createNegExpr(andExpr);
    return result;
  }

  /**
   * Transforms a conditional expr into a definite (\mu) expr.
   */
  public Object visitCondExpr(CondExpr term)
  {
    // transform the left expr
    Expr left = (Expr) term.getLeftExpr().accept(this);
    // transform the right expr
    Expr right = (Expr) term.getRightExpr().accept(this);
    // transforms the pred
    Pred pred = (Pred) term.getPred().accept(this);
    // \mu i: \{e_1, e_2\}
    Vector members = new Vector();
    members.add(left);
    members.add(right);
    SetExpr setExpr = factory_.createSetExpr(members);

    DeclName dn = factory_.createDeclName();
    dn.setWord("_i");
    Vector vars = new Vector();
    vars.add(dn);
    VarDecl var = factory_.createVarDecl(vars, setExpr);

    // i = e_1, i.e., (i, e_1) \mem (_ = _)
    Vector te1 = new Vector();
    RefExpr ref1 = factory_.createRefExpr();
    RefName refn1 = factory_.createRefName();
    refn1.setWord("_i");
    ref1.setRefName(refn1);
    te1.add(ref1);
    te1.add(left);
    TupleExpr tuple1 = factory_.createTupleExpr(te1);

    RefName eq = factory_.createRefName();
    eq.setWord("=");
    RefExpr equals = factory_.createRefExpr();
    equals.setRefName(eq);
    MemPred mem1 = factory_.createMemPred(tuple1, equals, new Boolean(false));

    // p \land i = e_1
    AndPred and1 = factory_.createAndPred(pred, mem1, Op.And);

    // i = e_2, i.e., (i, e_2) \mem (_ = _)
    Vector te2 = new Vector();
    te2.add(ref1);
    te2.add(right);

    TupleExpr tuple2 = factory_.createTupleExpr(te2);
    MemPred mem2 = factory_.createMemPred(tuple2, equals, new Boolean(false));

    // \lnot p
    NegPred neg = factory_.createNegPred(pred);
    // \lnot p \land i = e_2
    AndPred and2 = factory_.createAndPred(neg, mem2, Op.And);

    OrPred both = factory_.createOrPred(and1, and2);

    Vector varDecl = new Vector();
    varDecl.add(var);
    SchText schtxt = factory_.createSchText(varDecl, both);

    MuExpr mu = factory_.createMuExpr(schtxt, ref1);

    return mu;
  }

  /**
   * Transforms schema projection expr to set comprehension.
   */
  public Object visitProjExpr(ProjExpr term)
  {
    SchExpr left = (SchExpr) term.getLeftExpr().accept(this);
    SchExpr right = (SchExpr) term.getRightExpr().accept(this);
    // get NameExprPair from right
    Vector pairs = new Vector();
    SchText schtxt = right.getSchText();
    List decls = schtxt.getDecl();
    Decl de = null;
    for (int i = 0; i < decls.size(); i++) {
      de = (Decl) decls.get(i);
      if (de instanceof VarDecl) {
        Vector tmp = addNameExprPair((VarDecl) de);
        pairs.addAll(tmp);
      }
    }
    // binding construction \theta expr
    BindExpr be = factory_.createBindExpr(pairs);

    //schema text
    InclDecl dec1 = factory_.createInclDecl(left);
    InclDecl dec2 = factory_.createInclDecl(right);
    SchText st = factory_.createSchText();
    List schDecs = st.getDecl();
    schDecs.add(dec1);
    schDecs.add(dec2);

    // set comprehension
    SetCompExpr sce = factory_.createSetCompExpr(st, be);

    return sce;
  }

  /**
   * Transforms cartesian product into set comprehension.
   */
  public Object visitProdExpr(ProdExpr term)
  {
    List exprs = term.getExpr();
    Vector decls = new Vector();

    VarDecl vd = null;
    for (int i = 0; i < exprs.size(); i++) {
      vd = makeVarDecl((Expr) exprs.get(i), i);
      decls.add(vd);
    }

    // schema text
    SchText st = factory_.createSchText();
    List ds = st.getDecl();
    ds.addAll(decls);

    // tuple expr
    Vector refExprs = new Vector();

    RefExpr re = null;
    RefName rn = null;
    DeclName dn = null;
    for (int i = 0; i < exprs.size(); i++) {
      re = makeRefExpr(i);
      refExprs.add(re);
    }

    TupleExpr te = factory_.createTupleExpr();
    List tes = te.getExpr();
    tes.addAll(refExprs);

    SetCompExpr sce = factory_.createSetCompExpr(st, te);
    return sce;
  }

  private VarDecl makeVarDecl(Expr expr, int i)
  {
    DeclName dn = factory_.createDeclName();
    String varName = "_" + Integer.toString(i);
    dn.setWord(varName);
    VarDecl vd = factory_.createVarDecl();
    List vds = vd.getDeclName();
    vds.add(dn);
    vd.setExpr(expr);
    return vd;
  }

  private RefExpr makeRefExpr(int i)
  {
    RefExpr re = factory_.createRefExpr();
    DeclName dn = factory_.createDeclName();
    String varName = "_" + Integer.toString(i);
    dn.setWord(varName);
    RefName rn = factory_.createRefName();
    rn.setDecl(dn);
    re.setRefName(rn);
    return re;
  }

  /**
   * Transforms a ConstDecl into a VarDecl.
   */
  public Object visitConstDecl (ConstDecl term)
  {
    DeclName dn = term.getDeclName();
    Expr ex = term.getExpr();
    VarDecl vd = factory_.createVarDecl();
    List vds = vd.getDeclName();
    vds.add(dn);
    SetExpr ser = factory_.createSetExpr();
    List mem = ser.getExpr();
    mem.add(ex);
    vd.setExpr(ser);
    return vd;
  }
}
