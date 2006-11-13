/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
// TODO: change pred methods to be type void.
package net.sourceforge.czt.animation.eval;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.base.ast.Digit;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/** Flattens a Pred/Expr term into a list of FlatPred objects.
 *  The visit* methods add subclasses of Pred or Expr into the list flat_.
 *  Each visit*Expr method returns a Name, which is the name of the
 *  variable that will contain the result of the expression after evaulation.
 *  Each visit*Pred method returns null.
 *  <p>
 *  The ZLive parameter to the constructor is used to access the
 *  section manager (to get the current context of the expr/pred).
 */
public class FlattenVisitor
    implements
      TermVisitor<ZName>,
      AndPredVisitor<ZName>,
      OrPredVisitor<ZName>,
      ImpliesPredVisitor<ZName>,
      IffPredVisitor<ZName>,
      NegPredVisitor<ZName>,
      MemPredVisitor<ZName>,
      FalsePredVisitor<ZName>,
      TruePredVisitor<ZName>,
      ExistsPredVisitor<ZName>,
      ForallPredVisitor<ZName>,

      NumExprVisitor<ZName>,
      ApplExprVisitor<ZName>,
      TupleSelExprVisitor<ZName>,
      RefExprVisitor<ZName>,
      PowerExprVisitor<ZName>,
      SetExprVisitor<ZName>,
      SetCompExprVisitor<ZName>,
      MuExprVisitor<ZName>,
      ProdExprVisitor<ZName>,
      TupleExprVisitor<ZName>,
      BindExprVisitor<ZName>,
      ZNameVisitor<ZName>
{
  /** A reference to the main animator object, so that we can
      access all kinds of settings, tables and section manager etc.
  */
  private ZLive zlive_;

  /** A reference to the table of all visible definitions */
  private DefinitionTable table_;

  /** This list contains the result of flattening the expr/pred */
  private List<FlatPred> flat_;

  /** The set of builtin binary relations handled by ZLive */
  static final Set<String> knownRelations = new HashSet<String>();

  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  public FlattenVisitor(ZLive zlive, List<FlatPred> destination, DefinitionTable defns)
  {
    zlive_ = zlive;
    flat_ = destination;
    table_ = defns;
    VisitorUtils.checkVisitorRules(this);
    knownRelations.add(ZString.ARG_TOK+ZString.LESS+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.LEQ+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.GREATER+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.GEQ+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.NEQ+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.NOTMEM+ZString.ARG_TOK);
  }

  /** True if expr is a given set.
   *  We rely on the type annotations to determine this.
   *  But this is not enough, since x:\power CAR will have
   *  the same type as CAR.
   *
   *  TODO: The best way of identifying given sets would be
   *  to scan all the GivenParas and put those names into
   *  the definition table.  Probably something similar
   *  should be done with freetype names.
   */
  public boolean isGivenSet(RefExpr expr)
  {
    Object ann = expr.getAnn(TypeAnn.class);
    if (ann == null)
      return false;
    Type type = ((TypeAnn)ann).getType();
    if ( ! (type instanceof PowerType))
      return false;
    type = ((PowerType)type).getType();
    if ( ! (type instanceof GivenType))
      return false;
    GivenType gtype = (GivenType) type;
    if (((ZName)gtype.getName()).getWord().equals(ZString.ARITHMOS))
      return false;

    System.out.println("GivenSet "+((ZName)gtype.getName()).getWord()+".");
    return true;
  }

  /** True if expr is a member of a given set.
   *  We rely on the type annotations to determine this.
   *  As for isGivenSet, this is not enough, since in \forall x:CAR,
   *  we want to leave x as a normal variable, rather than
   *  converting it into a GivenValue.
   *  TODO: only classify global constants like this.
   *      (do this by putting appropriately typed global constants
   *      and freetype branches into the definition table, bound to
   *      a corresponding GivenValue).
   */
  public boolean isGivenValue(RefExpr expr)
  {
    Object ann = expr.getAnn(TypeAnn.class);
    if (ann == null)
      return false; // shouldn't happen
    Type type = ((TypeAnn)ann).getType();
    if ( ! (type instanceof GivenType))
      return false;
    GivenType gtype = (GivenType) type;
    if (((ZName) gtype.getName()).getWord().equals(ZString.ARITHMOS))
      return false;

    System.out.println("GivenValue "+((ZName) gtype.getName()).getWord()+".");
    return true;
  }

  /** Throws a 'not yet implemented' exception. */
  protected ZName notYet(Term t) {
    return notYet(t,"");
  }

  /** Throws a 'not yet implemented' exception. */
  protected ZName notYet(Term t, String msg) {
    throw new EvalException("ZLive does not handle "+t.getClass().getName()+" yet. " + msg, t);
  }

  /** Extracts the names of known binary relations. */
  protected String binaryRelation(Expr e) {
    if ( ! (e instanceof RefExpr))
      return null;
    ZName ref = ((RefExpr)e).getZName();
    if (ref.getZStrokeList().size() > 0)
      return null;
    String rel = ref.getWord();
    if (knownRelations.contains(rel))
      return rel;
    else
      return null;
  }

  /** An auxiliary method for visiting a list of Expr.
   *  @param  elements a list of Expr.
   *  @return an ArrayList of ZNames (same size as elements).
   */
  protected ArrayList<ZName> flattenExprList(
	   /*@non_null@*/List<Expr> elements)
  {
    ArrayList<ZName> refnames = new ArrayList<ZName>();
    for (Expr elem : elements)
      refnames.add(elem.accept(this));
    return refnames;
  }

  /** We throw an error if we reach a kind of term that we do not handle. */
  public ZName visitTerm(Term term) {
    if (term instanceof List)
      return (ZName) VisitorUtils.visitTerm(this,term,true);
    else
      return notYet(term);
  }

  /** Adds both conjuncts to the flatten list. */
  public ZName visitAndPred(AndPred p) {
    ((Pred)p.getLeftPred()).accept(this);
    ((Pred)p.getRightPred()).accept(this);
    return null;
  }

  /////////////// TODO: implement these, or unfold them //////////////////
  public ZName visitOrPred(OrPred p)
  {
    FlatPredList left = new FlatPredList(zlive_);
    left.addPred(p.getLeftPred());
    FlatPredList right = new FlatPredList(zlive_);
    right.addPred(p.getRightPred());
    flat_.add(new FlatOr(left, right));
    return null;
  }

  public ZName visitImpliesPred(ImpliesPred p) { return notYet(p); }
  public ZName visitIffPred(IffPred p) { return notYet(p); }
  public ZName visitNegPred(NegPred p) {
    FlatNot not = new FlatNot(zlive_);
    not.addPred(p.getPred());
    flat_.add(not);
    return null;
  }

  public ZName visitMemPred(MemPred p) {
    sLogger.entering("Flatten","visitMemPred");
    Factory factory = zlive_.getFactory();
    Expr lhs = p.getLeftExpr();
    Expr rhs = p.getRightExpr();
    String rel = null;
    if (rhs instanceof SetExpr
	&& ((SetExpr)rhs).getZExprList().size() == 1) {
      // We have an equality
      rhs = (Expr)((SetExpr)rhs).getZExprList().get(0);
      flat_.add(new FlatEquals(lhs.accept(this), rhs.accept(this)));
      sLogger.exiting("Flatten","visitMemPred","=");
      return null;
    }
    else if ((rel=binaryRelation(rhs)) != null
	     && lhs instanceof TupleExpr
	     && ((TupleExpr)lhs).getZExprList().size() == 2) {
      List<Expr> tuple = ((TupleExpr)lhs).getZExprList();
      ZName left = tuple.get(0).accept(this);
      ZName right = tuple.get(1).accept(this);
      if (rel.equals(ZString.ARG_TOK+ZString.LESS+ZString.ARG_TOK))
        flat_.add(new FlatLessThan(left,right));
      else if (rel.equals(ZString.ARG_TOK+ZString.LEQ+ZString.ARG_TOK))
          flat_.add(new FlatLessThanEquals(left,right));
      else if (rel.equals(ZString.ARG_TOK+ZString.GREATER+ZString.ARG_TOK))
        flat_.add(new FlatLessThan(right,left));
      else if (rel.equals(ZString.ARG_TOK+ZString.GEQ+ZString.ARG_TOK))
          flat_.add(new FlatLessThanEquals(right,left));
      else if (rel.equals(ZString.ARG_TOK+ZString.NEQ+ZString.ARG_TOK)) {
        // a \neq b  --> \lnot (a=b)
        RefExpr refLeft = factory.createRefExpr(left);
        RefExpr refRight = factory.createRefExpr(right);
        Pred tempp = factory.createEquality(refLeft, refRight);
        tempp = factory.createNegPred(tempp);
        tempp.accept(this);
      } else if (rel.equals(ZString.ARG_TOK+ZString.NOTMEM+ZString.ARG_TOK)) {
        // a \notin b  --> \lnot (a \in b)
        RefExpr refLeft = factory.createRefExpr(left);
        RefExpr refRight = factory.createRefExpr(right);
        Pred tempp = factory.createMemPred(refLeft, refRight, Boolean.FALSE);
        tempp = factory.createNegPred(tempp);
        tempp.accept(this);
      } else
        throw new EvalException("ERROR: unknown binary relation "+rel);
      }
    else {
	  flat_.add(new FlatMember(rhs.accept(this),
				   lhs.accept(this)));
    }
    sLogger.exiting("Flatten","visitMemPred");
    return null;
  }


  public ZName visitFalsePred(FalsePred p) {
   flat_.add(new FlatFalse());
   return null;
  }

  public ZName visitTruePred(TruePred p) {
    // Ignore it.
    return null;
  }

  public ZName visitExistsPred(ExistsPred p) {
    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(p.getZSchText());
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(p.getPred());
    flat_.add(new FlatExists(sch, body));
    return null;
  }

  public ZName visitForallPred(ForallPred p) {
    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(p.getZSchText());
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(p.getPred());
    flat_.add(new FlatForall(sch, body));
    return null;
  }

  /** Name objects are returned unchanged,
   *  except for \emptyset, which is unfolded into {}. */
  public ZName visitZName(ZName e)
  {
    if (e.getWord().equals(ZString.EMPTYSET) && e.getZStrokeList().isEmpty()) {
      ZName emptyset = zlive_.createNewName();
      flat_.add(new FlatDiscreteSet(new ArrayList<ZName>(), emptyset));
      e = emptyset;
    }
    return e;
  }

  /** Simple RefExpr objects are returned unchanged.
   *  We try to unfold non-generic definitions of names.
   *  We replace \nat and \num by FlatRangeSet.
   */
  public ZName visitRefExpr(RefExpr e) {
    if (e.getZExprList().size() != 0)
      return notYet(e, "generic");
    ZName result = e.getZName();
    // check for \nat and \num
    if ( result.getWord().equals(ZString.NAT)
        && result.getZStrokeList().isEmpty()) {
      result = zlive_.createNewName();
      ZName zeroName = zlive_.createNewName();
      Expr zero = zlive_.getFactory().createNumExpr(0);
      flat_.add(new FlatConst(zeroName, zero));
      flat_.add(new FlatRangeSet(zeroName,null,result));
    }
    else if ( result.getWord().equals(ZString.NAT)
        && result.getZStrokeList().size() == 1
        && (result.getZStrokeList().get(0) instanceof NumStroke)
        && ((NumStroke) result.getZStrokeList().get(0)).getDigit().equals(Digit.ONE)) {
      result = zlive_.createNewName();
      ZName oneName = zlive_.createNewName();
      Expr one = zlive_.getFactory().createNumExpr(1);
      flat_.add(new FlatConst(oneName, one));
      flat_.add(new FlatRangeSet(oneName,null,result));
    }
    else if (result.getWord().equals(ZString.NUM)
        && result.getZStrokeList().isEmpty()) {
      result = zlive_.createNewName();
      flat_.add(new FlatRangeSet(null,null,result));
    }
    else if (result.getWord().equals(ZString.ARITHMOS)
        && result.getZStrokeList().isEmpty()) {
      result = zlive_.createNewName();
      flat_.add(new FlatRangeSet(null,null,result));
    }
    else if (isGivenSet(e)) {
      flat_.add(new FlatGivenSet(result,result.getWord(),zlive_));
    }
    else if (isGivenValue(e)) {
      result = zlive_.createNewName();
      flat_.add(
          new FlatConst(result,
          new GivenValue(e.getZName().getWord())));
    }
    else {
      // Try to unfold this name via a (non-generic) definition.
      DefinitionTable.Definition def = null;
      // We only try to unfold undecorated names at the moment.
      if (e.getZName().getZStrokeList().isEmpty())
        def = table_.lookup(e.getZName().getWord());
      if (def != null && def.getDeclNames().size() == e.getZExprList().size()) {
        Expr newExpr = def.getExpr();
        result = newExpr.accept(this);
      }
    }
    return result;
  }

  /** NumExpr objects are converted into tmp = Num. */
  public ZName visitNumExpr(NumExpr e)
  {
    ZName result = zlive_.createNewName();
    flat_.add(new FlatConst(result,e));
    return result;
  }

  /** Used to allocate fresh temporary names in ApplExpr rewrites. */
  private static int applvar = 1;

  /** Each ApplExpr is flattened into a different kind of FlatPred. */
  public ZName visitApplExpr(ApplExpr e) {
    Expr func = (Expr) e.getLeftExpr();
    Expr arg = (Expr) e.getRightExpr();
    List<Expr> argList = null;
    ZName result = zlive_.createNewName();

    if (arg instanceof TupleExpr)
      argList = ((TupleExpr) arg).getZExprList();

    if (func instanceof RefExpr
        && ((RefExpr) func).getZName().getZStrokeList().size() == 0) {
      String funcname = ((RefExpr) func).getZName().getWord();
      if (funcname.equals(ZString.ARG_TOK + ZString.PLUS + ZString.ARG_TOK))
        flat_.add(new FlatPlus(
            argList.get(0).accept(this),
            argList.get(1).accept(this),
            result));
      else if (funcname.equals(ZString.ARG_TOK + ZString.MINUS + ZString.ARG_TOK))
        /* a-b=c <=> a=b+c (we could do this via a rewrite rule) */
        flat_.add(new FlatPlus(
            argList.get(1).accept(this),
	    result,
	    argList.get(0).accept(this)));
      else if (funcname.equals(ZString.ARG_TOK + ZString.MULT + ZString.ARG_TOK))
        flat_.add(new FlatMult(
            argList.get(0).accept(this),
            argList.get(1).accept(this),
            result));
      else if (funcname.equals(ZString.ARG_TOK + "div" + ZString.ARG_TOK))
        flat_.add(new FlatDiv(
            argList.get(0).accept(this),
            argList.get(1).accept(this),
            result));
      else if (funcname.equals(ZString.ARG_TOK + "mod" + ZString.ARG_TOK))
        flat_.add(new FlatMod(
            argList.get(0).accept(this),
            argList.get(1).accept(this),
            result));
      else if (funcname.equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK))
        flat_.add(new FlatRangeSet(
            argList.get(0).accept(this),
            argList.get(1).accept(this),
            result));
      else if (funcname.equals("#" + ZString.ARG_TOK)) {
        ZName argVar = arg.accept(this);
        flat_.add(new FlatCard(argVar, result));
      }
      else if (funcname.equals(ZString.NEG + ZString.ARG_TOK)) {
        ZName argVar = arg.accept(this);
        flat_.add(new FlatNegate(argVar, result));
      }
      else if (funcname.equals("succ" + ZString.ARG_TOK)) {
        /* succ _ = _ + 1; _ + 1 = result using FlatPlus */
        ZName argVar = arg.accept(this);
        Expr num1 = zlive_.getFactory().createNumExpr(1);
        ZName refForNum1 = num1.accept(this);
        flat_.add(new FlatPlus(argVar, refForNum1, result));
      }
      else if (funcname.equals(ZString.ARG_TOK + ZString.CUP + ZString.ARG_TOK)) {
          flat_.add(new FlatUnion(
            (ZName) argList.get(0).accept(this),
            (ZName) argList.get(1).accept(this),
            result));
      }
      // else if (...)   TODO: add more cases...
      else {
        return notYet(e, funcname);
      }
    }
    else {
      // Transform (func~arg) into (\mu p:func | p.1=arg @ p.2)
      // (this cannot be done at the same time as the preprocess rules,
      //  because we have to handle the above special cases first).
      Factory factory = zlive_.getFactory();
      // create the DeclList:  p:func
      ZStrokeList sl = factory.createZStrokeList();
      ZName pName =
        factory.createZName("p", sl, "ZLiveAppl"+(applvar++));
      ZNameList zdnl = factory.createZNameList();
      zdnl.add(pName);
      VarDecl decl = factory.createVarDecl(zdnl, func);
      ZDeclList decls = factory.createZDeclList(factory.list(decl));
      // create the predicate: p.1=arg
      Expr pRefExpr = factory.createRefExpr(pName);
      Expr p1 = factory.createTupleSelExpr(pRefExpr,factory.createZNumeral(1));
      Pred pred = factory.createEquality(p1,arg);
      ZSchText stext = factory.createZSchText(decls,pred);
      // create the expr: p.2
      Expr p2 = factory.createTupleSelExpr(pRefExpr,factory.createZNumeral(2));
      // create (\mu [p:func | p.1=arg] @ p.2)
      FlatPredList fp = new FlatPredList(zlive_);
      fp.addSchText(stext);
      result = fp.addExpr(p2);
      flat_.add(new FlatMu(fp, result));
    }
    return result;
  }

  public ZName visitTupleSelExpr(TupleSelExpr e)
  {
    ZName result = zlive_.createNewName();
    flat_.add(new FlatTupleSel(
            e.getExpr().accept(this),
            ((ZNumeral) e.getNumeral()).getValue().intValue(),
            result));
    return result;
  }

  public ZName visitPowerExpr(PowerExpr e) {
    ZName result = zlive_.createNewName();
    ZName base = e.getExpr().accept(this);
    flat_.add(new FlatPowerSet(base,result));
    return result;
  }

  public ZName visitSetExpr(SetExpr e)
  {
    ArrayList<ZName> refnames = flattenExprList(e.getZExprList());
    ZName result = zlive_.createNewName();
    flat_.add(new FlatDiscreteSet(refnames, result));
    return result;
  }

  public ZName visitSetCompExpr(SetCompExpr e) {
    ZName result = zlive_.createNewName();
    ZSchText text = e.getZSchText();
    List<Decl> decls = text.getZDeclList();
    Pred pred = text.getPred();
    Expr expr = e.getExpr();
    if (expr == null)
      expr = Flatten.charTuple(zlive_.getFactory(), decls);
    // We do not flatten decls/pred/expr, because FlatSetComp does it.
    flat_.add(new FlatSetComp(zlive_, decls, pred, expr, result));
    return result;
  }

  public ZName visitMuExpr(MuExpr e)
  {
    FlatPredList sch = new FlatPredList(zlive_);
    ZSchText stext = e.getZSchText();
    sch.addSchText(stext);
    Expr expr = e.getExpr();
    if (expr == null)
      expr = Flatten.charTuple(zlive_.getFactory(), stext.getZDeclList());
    ZName resultName = sch.addExpr(expr);
    flat_.add(new FlatMu(sch, resultName));
    return resultName;
  }

  public ZName visitProdExpr(ProdExpr e) {
    ArrayList<ZName> refnames = flattenExprList(e.getZExprList());
    ZName result = zlive_.createNewName();
    flat_.add(new FlatProd(refnames, result));
    return result;
  }

  public ZName visitTupleExpr(TupleExpr e) {
    ArrayList<ZName> refnames = flattenExprList(e.getZExprList());
    ZName result = zlive_.createNewName();
    flat_.add(new FlatTuple(refnames, result));
    return result;
  }

  public ZName visitBindExpr(BindExpr e)
  {
    List<ZName> names = new ArrayList<ZName>();
    List<ZName> exprs = new ArrayList<ZName>();
    for (Decl decl : e.getZDeclList()) {
      ConstDecl constDecl = (ConstDecl) decl;
      names.add(constDecl.getZName());
      exprs.add(constDecl.getExpr().accept(this)); // recursive flatten
    }
    ZName result = zlive_.createNewName();
    flat_.add(new FlatBinding(names, exprs, result));
    return result;
  }

  /*
  public ZDeclList visitZDeclList(ZDeclList declList)
  {
    // TODO: clean up the types here.  Can we avoid the casts?
    List<Decl> declList2 = (List<Decl>) declList.getZDeclList().accept(this);
    return zlive_.getFactory().createZDeclList(declList2);
  }
  */

/*
  public ZName visitFreetype(Freetype zedObject) { return zedObject; }
  public ZName visitNameNamePair(NameNamePair zedObject) {return zedObject; }
  public ZName visitLetExpr(LetExpr zedObject) {return zedObject; }
  public ZName visitSignature(Signature zedObject) {return zedObject; }
  public ZName visitProdType(ProdType zedObject) {return zedObject; }
  public ZName visitDecl(Decl zedObject) {return zedObject; }
  public ZName visitConstDecl(ConstDecl zedObject) {return zedObject; }
  public ZName visitImpliesExpr(ImpliesExpr zedObject) {return zedObject; }
  public ZName visitSchExpr2(SchExpr2 zedObject) {return zedObject; }
  public ZName visitExistsExpr(ExistsExpr zedObject) {return zedObject; }
  public ZName visitExists1Expr(Exists1Expr zedObject) {return zedObject; }
  public ZName visitForallExpr(ForallExpr zedObject) {return zedObject; }
  public ZName visitVarDecl(VarDecl zedObject) {return zedObject; }
  public ZName visitCompExpr(CompExpr zedObject) {return zedObject; }
  public ZName visitCondExpr(CondExpr zedObject) {return zedObject; }
  public ZName visitLambdaExpr(LambdaExpr zedObject) {return zedObject; }
  public ZName visitIffExpr(IffExpr zedObject) {return zedObject; }
  public ZName visitQntExpr(QntExpr zedObject) {return zedObject; }
  public ZName visitNameTypePair(NameTypePair zedObject) {return zedObject; }
  public ZName visitSchText(SchText zedObject) {return zedObject; }
  public ZName visitQnt1Expr(Qnt1Expr zedObject) {return zedObject; }
  public ZName visitOperand(Operand zedObject) {return zedObject; }
  public ZName visitProjExpr(ProjExpr zedObject) {return zedObject; }
  public ZName visitBranch(Branch zedObject) {return zedObject; }
  public ZName visitGenType(GenType zedObject) {return zedObject; }
  public ZName visitPreExpr(PreExpr zedObject) {return zedObject; }
  public ZName visitExprPred(ExprPred zedObject) {return zedObject; }
  public ZName visitGivenType(GivenType zedObject) {return zedObject; }
  public ZName visitInclDecl(InclDecl zedObject) {return zedObject; }
  public ZName visitPred(Pred zedObject) {return zedObject; }
  public ZName visitSchemaType(SchemaType zedObject) {return zedObject; }
  public ZName visitBindSelExpr(BindSelExpr zedObject) {return zedObject; }
  public ZName visitName(Name zedObject) {return zedObject; }
  public ZName visitOrExpr(OrExpr zedObject) {return zedObject; }
  public ZName visitSpec(Spec zedObject) {return zedObject; }
  public ZName visitHideExpr(HideExpr zedObject) {return zedObject; }
  public ZName visitPowerType(PowerType zedObject) {return zedObject; }
  public ZName visitAndExpr(AndExpr zedObject) {return zedObject; }
  public ZName visitRenameExpr(RenameExpr zedObject) {return zedObject; }
  public ZName visitThetaExpr(ThetaExpr zedObject) {return zedObject; }
  public ZName visitPipeExpr(PipeExpr zedObject) {return zedObject; }
  public ZName visitNegExpr(NegExpr zedObject) {return zedObject; }
  public ZName visitDecorExpr(DecorExpr zedObject) {return zedObject; }
  public ZName visitExists1Pred(Exists1Pred zedObject) {return zedObject; }
  public ZName visitSchExpr(SchExpr zedObject) {return zedObject; }
*/
}

