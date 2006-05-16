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

import java.util.*;
import java.util.logging.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z.util.ZString;

import net.sourceforge.czt.animation.eval.flatpred.*;

/** Flattens a Pred/Expr term into a list of FlatPred objects.
 *  The visit* methods add subclasses of Pred or Expr into the list flat_.
 *  Each visit*Expr method returns a RefName, which is the name of the
 *  variable that will contain the result of the expression after evaulation.
 *  Each visit*Pred method returns null.
 *  <p>
 *  The ZLive parameter to the constructor is used to access the
 *  section manager (to get the current context of the expr/pred).
 */
public class FlattenVisitor
    implements
      TermVisitor<ZRefName>,
      AndPredVisitor<ZRefName>,
      OrPredVisitor<ZRefName>,
      ImpliesPredVisitor<ZRefName>,
      IffPredVisitor<ZRefName>,
      NegPredVisitor<ZRefName>,
      MemPredVisitor<ZRefName>,
      FalsePredVisitor<ZRefName>,
      TruePredVisitor<ZRefName>,
      ExistsPredVisitor<ZRefName>,
      ForallPredVisitor<ZRefName>,

      NumExprVisitor<ZRefName>,
      ApplExprVisitor<ZRefName>,
      TupleSelExprVisitor<ZRefName>,
      RefExprVisitor<ZRefName>,
      PowerExprVisitor<ZRefName>,
      SetExprVisitor<ZRefName>,
      SetCompExprVisitor<ZRefName>,
      MuExprVisitor<ZRefName>,
      ProdExprVisitor<ZRefName>,
      TupleExprVisitor<ZRefName>,
      BindExprVisitor<ZRefName>,
      ZRefNameVisitor<ZRefName>
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
    if (gtype.getName().getWord().equals(ZString.ARITHMOS))
      return false;
    
    System.out.println("GivenSet "+gtype.getName().getWord()+".");
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
    if (gtype.getName().getWord().equals(ZString.ARITHMOS))
      return false;
    
    System.out.println("GivenValue "+gtype.getName().getWord()+".");
    return true;
  }

  /** Throws a 'not yet implemented' exception. */
  protected ZRefName notYet(Term t) {
    return notYet(t,"");
  }

  /** Throws a 'not yet implemented' exception. */
  protected ZRefName notYet(Term t, String msg) {
    throw new EvalException("ZLive does not handle "+t.getClass().getName()+" yet. " + msg, t);
  }

  /** Extracts the names of known binary relations. */
  protected String binaryRelation(Expr e) {
    if ( ! (e instanceof RefExpr))
      return null;
    ZRefName ref = ((RefExpr)e).getZRefName();
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
   *  @return an ArrayList of ZRefNames (same size as elements).
   */ 
  protected ArrayList<ZRefName> flattenExprList(
	   /*@non_null@*/List<Expr> elements)
  {
    ArrayList<ZRefName> refnames = new ArrayList<ZRefName>();
    for (Expr elem : elements)
      refnames.add(elem.accept(this));
    return refnames;
  }

  /** We throw an error if we reach a kind of term that we do not handle. */
  public ZRefName visitTerm(Term term) {
    if (term instanceof List)
      return (ZRefName) VisitorUtils.visitTerm(this,term,true);
    else
      return notYet(term);
  }

  /** Adds both conjuncts to the flatten list. */
  public ZRefName visitAndPred(AndPred p) {
    ((Pred)p.getLeftPred()).accept(this);
    ((Pred)p.getRightPred()).accept(this);
    return null;
  }

  /////////////// TODO: implement these, or unfold them //////////////////
  public ZRefName visitOrPred(OrPred p)
  {
    FlatPredList left = new FlatPredList(zlive_);
    left.addPred(p.getLeftPred());
    FlatPredList right = new FlatPredList(zlive_);
    right.addPred(p.getRightPred());
    flat_.add(new FlatOr(left, right));
    return null;
  }
  
  public ZRefName visitImpliesPred(ImpliesPred p) { return notYet(p); }
  public ZRefName visitIffPred(IffPred p) { return notYet(p); }
  public ZRefName visitNegPred(NegPred p) {
    FlatNot not = new FlatNot(zlive_);
    not.addPred(p.getPred());
    flat_.add(not);
    return null;
  }

  public ZRefName visitMemPred(MemPred p) {
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
      ZRefName left = tuple.get(0).accept(this);
      ZRefName right = tuple.get(1).accept(this);
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


  public ZRefName visitFalsePred(FalsePred p) {
   flat_.add(new FlatFalse());
   return null;
  }

  public ZRefName visitTruePred(TruePred p) {
    // Ignore it.
    return null;
  }

  public ZRefName visitExistsPred(ExistsPred p) {
    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(p.getZSchText());
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(p.getPred());
    flat_.add(new FlatExists(sch, body));
    return null;
  }

  public ZRefName visitForallPred(ForallPred p) {
    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(p.getZSchText());
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(p.getPred());
    flat_.add(new FlatForall(sch, body));
    return null;
  }

  /** Name objects are returned unchanged. */
  public ZRefName visitZRefName(ZRefName e)
  { return e; }

  /** Simple RefExpr objects are returned unchanged.
   *  We try to unfold non-generic definitions of names.
   *  We replace \nat and \num by FlatRangeSet.
   */
  public ZRefName visitRefExpr(RefExpr e) {
    if (e.getZExprList().size() != 0)
      return notYet(e, "generic");
    ZRefName result = e.getZRefName();
    // check for \nat and \num
    if ( result.getWord().equals(ZString.NAT)
        && result.getZStrokeList().isEmpty()) {
      result = zlive_.createNewName();
      ZRefName zeroName = zlive_.createNewName();
      Expr zero = zlive_.getFactory().createNumExpr(0);
      flat_.add(new FlatConst(zeroName, zero));
      flat_.add(new FlatRangeSet(zeroName,null,result));
    }
    else if ( result.getWord().equals(ZString.NAT)
        && result.getZStrokeList().size() == 1
        && (result.getZStrokeList().get(0) instanceof NumStroke)
        && ((NumStroke) result.getZStrokeList().get(0)).getDigit().equals(Digit.ONE)) {
      result = zlive_.createNewName();
      ZRefName oneName = zlive_.createNewName();
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
          new GivenValue(e.getZRefName().getWord())));
    }
    else {
      // Try to unfold this name via a (non-generic) definition.
      DefinitionTable.Definition def = null;
      // We only try to unfold undecorated names at the moment.
      if (e.getZRefName().getZStrokeList().isEmpty())
        def = table_.lookup(e.getZRefName().getWord());
      if (def != null && def.getDeclNames().size() == e.getZExprList().size()) {
        Expr newExpr = def.getExpr();
        result = newExpr.accept(this);      
      }
    }
    return result;
  }

  /** NumExpr objects are converted into tmp = Num. */
  public ZRefName visitNumExpr(NumExpr e)
  {     
    ZRefName result = zlive_.createNewName();
    flat_.add(new FlatConst(result,e));
    return result;
  }

  /** Used to allocate fresh temporary names in ApplExpr rewrites. */
  private static int applvar = 1;

  /** Each ApplExpr is flattened into a different kind of FlatPred. */
  public ZRefName visitApplExpr(ApplExpr e) {
    Expr func = (Expr) e.getLeftExpr();
    Expr arg = (Expr) e.getRightExpr();
    List<Expr> argList = null;
    ZRefName result = zlive_.createNewName();

    if (arg instanceof TupleExpr)
      argList = ((TupleExpr) arg).getZExprList();

    if (func instanceof RefExpr
        && ((RefExpr) func).getZRefName().getZStrokeList().size() == 0) {
      String funcname = ((RefExpr) func).getZRefName().getWord();
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
        ZRefName argVar = arg.accept(this);
        flat_.add(new FlatCard(argVar, result));
      }
      else if (funcname.equals(ZString.NEG + ZString.ARG_TOK)) {
        ZRefName argVar = arg.accept(this);
        flat_.add(new FlatNegate(argVar, result));
      }
      else if (funcname.equals("succ" + ZString.ARG_TOK)) {
        /* succ _ = _ + 1; _ + 1 = result using FlatPlus */        
        ZRefName argVar = arg.accept(this);
        Expr num1 = zlive_.getFactory().createNumExpr(1);
        ZRefName refForNum1 = num1.accept(this);
        flat_.add(new FlatPlus(argVar, refForNum1, result));        
      } 
      else if (funcname.equals(ZString.ARG_TOK + ZString.CUP + ZString.ARG_TOK)) {
          flat_.add(new FlatUnion(
            (ZRefName) argList.get(0).accept(this),
            (ZRefName) argList.get(1).accept(this), 
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
      ZDeclName pDeclName = factory.createZDeclName("p",null,
          "ZLiveAppl"+(applvar++));
      ZRefName pRefName = factory.createZRefName("p",null,pDeclName);
      VarDecl decl = factory.createVarDecl(factory.list(pDeclName),func);
      ZDeclList decls = factory.createZDeclList(factory.list(decl));
      // create the predicate: p.1=arg
      Expr pRefExpr = factory.createRefExpr(pRefName);
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

  public ZRefName visitTupleSelExpr(TupleSelExpr e)
  {
    ZRefName result = zlive_.createNewName();
    flat_.add(new FlatTupleSel(
            e.getExpr().accept(this),
            ((ZNumeral) e.getNumeral()).getValue().intValue(),
            result));
    return result;
  }

  public ZRefName visitPowerExpr(PowerExpr e) {
    return notYet(e);
  }
  
  public ZRefName visitSetExpr(SetExpr e) 
  {
    ArrayList<ZRefName> refnames = flattenExprList(e.getZExprList());
    ZRefName result = zlive_.createNewName();
    flat_.add(new FlatDiscreteSet(refnames, result));
    return result;
  }

  public ZRefName visitSetCompExpr(SetCompExpr e) {
    ZRefName result = zlive_.createNewName();
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

  public ZRefName visitMuExpr(MuExpr e)
  {
    FlatPredList sch = new FlatPredList(zlive_);
    ZSchText stext = e.getZSchText();
    sch.addSchText(stext);
    Expr expr = e.getExpr();
    if (expr == null)
      expr = Flatten.charTuple(zlive_.getFactory(), stext.getZDeclList());
    ZRefName resultName = sch.addExpr(expr);
    flat_.add(new FlatMu(sch, resultName));
    return resultName;
  }

  public ZRefName visitProdExpr(ProdExpr e) {
    return notYet(e);
  }

  public ZRefName visitTupleExpr(TupleExpr e) {
    ArrayList<ZRefName> refnames = flattenExprList(e.getZExprList());
    ZRefName result = zlive_.createNewName();
    flat_.add(new FlatTuple(refnames, result));
    return result;
  }

  public ZRefName visitBindExpr(BindExpr e)
  {
    List<ZDeclName> names = new ArrayList<ZDeclName>();
    List<ZRefName>  exprs = new ArrayList<ZRefName>();
    for (Decl decl : e.getZDeclList()) {
      ConstDecl constDecl = (ConstDecl) decl;
      names.add(constDecl.getZDeclName());
      exprs.add(constDecl.getExpr().accept(this)); // recursive flatten
    }
    ZRefName result = zlive_.createNewName();
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
  public ZRefName visitFreetype(Freetype zedObject) { return zedObject; }
  public ZRefName visitNameNamePair(NameNamePair zedObject) {return zedObject; }
  public ZRefName visitLetExpr(LetExpr zedObject) {return zedObject; }
  public ZRefName visitSignature(Signature zedObject) {return zedObject; }
  public ZRefName visitProdType(ProdType zedObject) {return zedObject; }
  public ZRefName visitDecl(Decl zedObject) {return zedObject; }
  public ZRefName visitConstDecl(ConstDecl zedObject) {return zedObject; }
  public ZRefName visitImpliesExpr(ImpliesExpr zedObject) {return zedObject; }
  public ZRefName visitSchExpr2(SchExpr2 zedObject) {return zedObject; }
  public ZRefName visitExistsExpr(ExistsExpr zedObject) {return zedObject; }
  public ZRefName visitExists1Expr(Exists1Expr zedObject) {return zedObject; }
  public ZRefName visitForallExpr(ForallExpr zedObject) {return zedObject; }
  public ZRefName visitVarDecl(VarDecl zedObject) {return zedObject; }
  public ZRefName visitCompExpr(CompExpr zedObject) {return zedObject; }
  public ZRefName visitCondExpr(CondExpr zedObject) {return zedObject; }
  public ZRefName visitLambdaExpr(LambdaExpr zedObject) {return zedObject; }
  public ZRefName visitIffExpr(IffExpr zedObject) {return zedObject; }
  public ZRefName visitQntExpr(QntExpr zedObject) {return zedObject; }
  public ZRefName visitNameTypePair(NameTypePair zedObject) {return zedObject; }
  public ZRefName visitSchText(SchText zedObject) {return zedObject; }
  public ZRefName visitQnt1Expr(Qnt1Expr zedObject) {return zedObject; }
  public ZRefName visitOperand(Operand zedObject) {return zedObject; }
  public ZRefName visitProjExpr(ProjExpr zedObject) {return zedObject; }
  public ZRefName visitBranch(Branch zedObject) {return zedObject; }
  public ZRefName visitGenType(GenType zedObject) {return zedObject; }
  public ZRefName visitPreExpr(PreExpr zedObject) {return zedObject; }
  public ZRefName visitExprPred(ExprPred zedObject) {return zedObject; }
  public ZRefName visitGivenType(GivenType zedObject) {return zedObject; }
  public ZRefName visitInclDecl(InclDecl zedObject) {return zedObject; }
  public ZRefName visitPred(Pred zedObject) {return zedObject; }
  public ZRefName visitSchemaType(SchemaType zedObject) {return zedObject; }
  public ZRefName visitBindSelExpr(BindSelExpr zedObject) {return zedObject; }
  public ZRefName visitDeclName(DeclName zedObject) {return zedObject; }
  public ZRefName visitOrExpr(OrExpr zedObject) {return zedObject; }
  public ZRefName visitSpec(Spec zedObject) {return zedObject; }
  public ZRefName visitHideExpr(HideExpr zedObject) {return zedObject; }
  public ZRefName visitPowerType(PowerType zedObject) {return zedObject; }
  public ZRefName visitAndExpr(AndExpr zedObject) {return zedObject; }
  public ZRefName visitRenameExpr(RenameExpr zedObject) {return zedObject; }
  public ZRefName visitThetaExpr(ThetaExpr zedObject) {return zedObject; }
  public ZRefName visitPipeExpr(PipeExpr zedObject) {return zedObject; }
  public ZRefName visitNegExpr(NegExpr zedObject) {return zedObject; }
  public ZRefName visitDecorExpr(DecorExpr zedObject) {return zedObject; }
  public ZRefName visitExists1Pred(Exists1Pred zedObject) {return zedObject; }
  public ZRefName visitSchExpr(SchExpr zedObject) {return zedObject; }
*/
}

