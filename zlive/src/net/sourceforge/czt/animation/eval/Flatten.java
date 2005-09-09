/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

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
package net.sourceforge.czt.animation.eval;

import java.util.*;
import java.util.logging.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z.util.ZString;

import net.sourceforge.czt.animation.eval.*;
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
public class Flatten
    implements
      TermVisitor,
      AndPredVisitor,
      OrPredVisitor,
      ImpliesPredVisitor,
      IffPredVisitor,
      NegPredVisitor,
      MemPredVisitor,
      FalsePredVisitor,
      TruePredVisitor,
      ExistsPredVisitor,
      ForallPredVisitor,

      NameVisitor,
      NumExprVisitor,
      ApplExprVisitor,
      TupleSelExprVisitor,
      RefExprVisitor,
      PowerExprVisitor,
      SetExprVisitor,
      SetCompExprVisitor,
      ProdExprVisitor,
      TupleExprVisitor,
      BindExprVisitor,
      ConstDeclVisitor,
      ZDeclListVisitor
{
  private ZLive zlive_;
  
  private DefinitionTable table_;

  private List flat_;

  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  /** Throws a 'not yet implemented' exception. */
  protected Term notYet(Term t) {
    return notYet(t,"");
  }

  /** Throws a 'not yet implemented' exception. */
  protected Term notYet(Term t, String msg) {
    throw new RuntimeException("Flatten does not yet handle: " + t
			       + "   ("+msg+")");
  }

  public Flatten(ZLive zlive)
  {
    zlive_ = zlive;
    VisitorUtils.checkVisitorRules(this);
    knownRelations.add(ZString.ARG_TOK+ZString.LESS+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.LEQ+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.GREATER+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.GEQ+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.NEQ+ZString.ARG_TOK);
    knownRelations.add(ZString.ARG_TOK+ZString.NOTMEM+ZString.ARG_TOK);    
  }

  /** Flattens the toFlatten predicate into a list of FlatPred predicates.
   *  @param  toFlatten The Pred to flatten.
   *  @param  destination Generated FlatPred objects are appended to this list.
   */
  public void flattenPred(Pred toFlatten, List destination)
    throws CommandException
  {
    flat_ = destination;
    String currSect = zlive_.getCurrentSection();
    Key key = new Key(currSect, DefinitionTable.class);
    table_ = (DefinitionTable) zlive_.getSectionManager().get(key);
    toFlatten.accept(this);
  }

  /** Flattens the toFlatten expression into a list of FlatPred predicates.
   *  @param  toFlatten An Expr to flatten.
   *  @param  destination Generated FlatPred objects are appended to this list.
   *  @return The name of the variable that will contain the result,
   *          after evaluation.
   */
  public RefName flattenExpr(Expr toFlatten, List destination)
    throws CommandException
  {
    flat_ = destination;
    String currSect = zlive_.getCurrentSection();
    Key key = new Key(currSect, DefinitionTable.class);
    table_ = (DefinitionTable) zlive_.getSectionManager().get(key);
    return (RefName)toFlatten.accept(this);
  }  
 
  /** An auxiliary method for flattening a list of Decl in a Map. */
  protected List/*<DeclName>*/ declNames(List decls) {
    List result = new ArrayList();
    for (Iterator i = decls.iterator(); i.hasNext();) {
      Decl decl = (Decl) i.next();
      if (decl instanceof VarDecl) {
        VarDecl vdecl = (VarDecl) decl;
        Iterator id = vdecl.getDeclName().iterator();
        while (id.hasNext()) {
          DeclName name = (DeclName)id.next();
          result.add(name);
        }
      }
      else if (decl instanceof ConstDecl) {
        ConstDecl cdecl = (ConstDecl) decl;
        DeclName name = cdecl.getDeclName();
        result.add(name);
      }
      else {
        throw new EvalException("Unknown kind of Decl: " + decl);
      }
    }
    return result;
  }

  static final Set knownRelations = new HashSet();
  
  /** Extracts the names of known binary relations. */
  protected String binaryRelation(Expr e) {
    if ( ! (e instanceof RefExpr))
      return null;
    RefName ref = ((RefExpr)e).getRefName();
    if (ref.getStroke().size() > 0)
      return null;
    String rel = ref.getWord();
    if (knownRelations.contains(rel))
      return rel;
    else
      return null;
  }
  
  /** An auxiliary method for visiting a list of Expr.
   *  @param  elements a list of Expr.
   *  @return an ArrayList of RefNames (same size as elements).
   */ 
  protected ArrayList/*<RefName>*/ flattenExprList(
	   /*@non_null@*/List/*<Expr>*/ elements)
  {
    ArrayList refnames = new ArrayList();
    for (Iterator i = elements.iterator(); i.hasNext(); ) {
      Expr elem = (Expr)i.next();
      refnames.add(elem.accept(this));
    }
    return refnames;
  }

  /** We throw an error if we reach a kind of term that we do not handle. */
  public Object visitTerm(Term term) {
    if (term instanceof List)
      return VisitorUtils.visitTerm(this,term,true);
    else
      return notYet(term);
  }

  /** Adds both conjuncts to the flatten list. */
  public Object visitAndPred(AndPred p) {
    ((Pred)p.getLeftPred()).accept(this);
    ((Pred)p.getRightPred()).accept(this);
    return null;
  }

  /////////////// TODO: implement these, or unfold them //////////////////
  public Object visitOrPred(OrPred p) { return notYet(p); }
  public Object visitImpliesPred(ImpliesPred p) { return notYet(p); }
  public Object visitIffPred(IffPred p) { return notYet(p); }
  public Object visitNegPred(NegPred p) {
    FlatPredList inner = new FlatPredList(zlive_);
    inner.addPred(p.getPred());
    flat_.add(new FlatNot(inner));
    return null;
  }

  public Object visitMemPred(MemPred p) {
    sLogger.entering("Flatten","visitMemPred");
    Factory factory = zlive_.getFactory();
    Expr lhs = p.getLeftExpr();
    Expr rhs = p.getRightExpr();
    if (rhs instanceof SetExpr
	&& ((SetExpr)rhs).getExpr().size() == 1) {
      // We have an equality
      rhs = (Expr)((SetExpr)rhs).getExpr().get(0);
      flat_.add(new FlatEquals((RefName)lhs.accept(this),
			       (RefName)rhs.accept(this)));
      return null;
    }
    else if (binaryRelation(rhs) != null
	     && lhs instanceof TupleExpr
	     && ((TupleExpr)lhs).getExpr().size() == 2) {
      String rel = binaryRelation(rhs);
      List tuple = ((TupleExpr)lhs).getExpr();
      RefName left = (RefName)((Expr)tuple.get(0)).accept(this);
      RefName right = (RefName)((Expr)tuple.get(1)).accept(this);
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
	  flat_.add(new FlatMember((RefName)rhs.accept(this), 
				 (RefName)lhs.accept(this)));
    }
    sLogger.exiting("Flatten","visitMemPred");
    return null;
  }


  public Object visitFalsePred(FalsePred p) {
   flat_.add(new FlatFalse());
   return null;
  }

  public Object visitTruePred(TruePred p) {
    // Ignore it.
    return null;
  }

  public Object visitExistsPred(ExistsPred p) {
    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(p.getSchText());
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(p.getPred());
    flat_.add(new FlatExists(sch, body));
    return null;
  }

  public Object visitForallPred(ForallPred p) {
    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(p.getSchText());
    FlatPredList body = new FlatPredList(zlive_);
    body.addPred(p.getPred());
    flat_.add(new FlatForall(sch, body));
    return null;
  }

  /** Name objects are returned unchanged. */
  public Object visitName(Name e)
  { return e; }

  /** Simple RefExpr objects are returned unchanged. */
  public Object visitRefExpr(RefExpr e) {
    if (e.getExpr().size() != 0)
	return notYet(e, "generic");
    // Try to unfold this name via a definition.
    DefinitionTable.Definition def = table_.lookup(e.getRefName().toString());
    if (def != null && def.getDeclNames().size() == e.getExpr().size()) {
      Expr newExpr = def.getExpr();
      return newExpr.accept(this);      
    }
    return e.getRefName();
  }

  /** NumExpr objects are converted into tmp = Num. */
  public Object visitNumExpr(NumExpr e)
  {     
    RefName result = zlive_.createNewName();
    flat_.add(new FlatConst(result,e));
    return result;
  }

  /** Each ApplExpr is flattened into a different kind of FlatPred. */
  public Object visitApplExpr(ApplExpr e) {
    Expr func = (Expr) e.getLeftExpr();
    Expr arg = (Expr) e.getRightExpr();
    List argList = null;
    RefName result = zlive_.createNewName();

    if (arg instanceof TupleExpr)
      argList = ((TupleExpr) arg).getExpr();

    if (func instanceof RefExpr
        && ((RefExpr) func).getRefName().getStroke().size() == 0) {
      String funcname = ((RefExpr) func).getRefName().getWord();
      if (funcname.equals(ZString.ARG_TOK + ZString.PLUS + ZString.ARG_TOK)) 
        flat_.add(new FlatPlus(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + ZString.MINUS + ZString.ARG_TOK)) 
        /* a-b=c <=> a=b+c (we could do this via a rewrite rule) */
        flat_.add(new FlatPlus(
            (RefName)((Expr)argList.get(1)).accept(this),
	    result,
	    (RefName)((Expr)argList.get(0)).accept(this)));
      else if (funcname.equals(ZString.ARG_TOK + ZString.MULT + ZString.ARG_TOK))
        flat_.add(new FlatMult(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + "div" + ZString.ARG_TOK))
        flat_.add(new FlatDiv(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + "mod" + ZString.ARG_TOK))
        flat_.add(new FlatMod(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK))
        flat_.add(new FlatRangeSet(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      else if (funcname.equals("#" + ZString.ARG_TOK)) {
        RefName argVar = (RefName) arg.accept(this);
        flat_.add(new FlatCard(argVar, result));
      }
      else if (funcname.equals(ZString.NEG + ZString.ARG_TOK)) {
        RefName argVar = (RefName) arg.accept(this);
        flat_.add(new FlatNegate(argVar, result));
      }
      else if (funcname.equals("succ" + ZString.ARG_TOK)) {
        /* succ _ = _ + 1; _ + 1 = result using FlatPlus */        
        RefName argVar = (RefName) arg.accept(this);
        Expr num1 = zlive_.getFactory().createNumExpr(1);
        RefName refForNum1 = (RefName)num1.accept(this);
        flat_.add(new FlatPlus(argVar, refForNum1, result));        
      } 
      else if (funcname.equals(ZString.ARG_TOK + ZString.CUP + ZString.ARG_TOK)) {
          flat_.add(new FlatUnion(
            (RefName)((Expr)argList.get(0)).accept(this),
            (RefName)((Expr)argList.get(1)).accept(this), 
            result));
      }
      // else if (...)   TODO: add more cases...
      else {
	return notYet(e, funcname);
        // TODO: flat_.add(new FlatAppl(func, args, result));
      }
    }
    else {
	return notYet(e, "Function="+func);
    }
    return result;
  }

  public Object visitTupleSelExpr(TupleSelExpr e)
  {
    RefName result = zlive_.createNewName();
    flat_.add(new FlatTupleSel(
            (RefName)((Expr) e.getExpr()).accept(this),
            e.getSelect(),
            result));
    return result;
  }

  public Object visitPowerExpr(PowerExpr e) { return notYet(e); }
  
  public Object visitSetExpr(SetExpr e) 
  {
    ArrayList refnames = flattenExprList(e.getExpr());
    RefName result = zlive_.createNewName();
    flat_.add(new FlatDiscreteSet(refnames, result));
    return result;
  }
  
  public Object visitSetCompExpr(SetCompExpr e) {
    RefName result = zlive_.createNewName();
    SchText text = e.getSchText();
    List decls = ((ZDeclList) text.getDeclList()).getDecl();
    Pred pred = text.getPred();
    Expr expr = e.getExpr();
    if (expr == null) {
      List names = declNames(decls);
      if (names.size() == 0)
        throw new EvalException("empty set comprehension!");
      else if (names.size() == 1) {
        RefName refName = zlive_.getFactory().createRefName((DeclName)names.get(0));
        expr = zlive_.getFactory().createRefExpr(refName);
      }
      else {
        // Make a tuple!
        List/*<RefExpr>*/ refExprs = new ArrayList();
        for (Iterator i = names.iterator(); i.hasNext(); ) {
          RefName tmpName = zlive_.getFactory().createRefName((DeclName)i.next());
          refExprs.add(zlive_.getFactory().createRefExpr(tmpName));
        }
        expr = zlive_.getFactory().createTupleExpr(refExprs);
      }
    }
    // We do not flatten decls/pred/expr, because FlatSetComp does it.
    flat_.add(new FlatSetComp(zlive_, decls, pred, expr, result));
    return result;
  }

  public Object visitProdExpr(ProdExpr e) { return notYet(e); }
  public Object visitTupleExpr(TupleExpr e) {
    ArrayList refnames = flattenExprList(e.getExpr());
    RefName result = zlive_.createNewName();
    flat_.add(new FlatTuple(refnames, result));
    return result;
  }

  public Object visitBindExpr(BindExpr e)
  {
    return notYet(e);
    /*
    ZDeclList decls = (ZDeclList) e.getDeclList().accept(this);
    RefName result = zlive_.createNewName();
    flat_.add(new FlatBinding(decls, result));
    return result;
    */
  }

  public Object visitZDeclList(ZDeclList declList)
  {
    List<Decl> declList2 = (List<Decl>) declList.getDecl().accept(this);
    return zlive_.getFactory().createZDeclList(declList2);
  }

  /** Handles the ConstDecls that appear within BindExpr.
   *  Unlike most other visit methods in this class, this does not return
   *  just a RefName.  Instead it returns a new ConstDecl, which should be
   *  handled by the callers of this method (BindExpr). This is because 
   *  these ConstDecls are really part of the syntax of the BindExpr,
   *  rather than a separate Z operator.
   *  @param  constDecl A ConstDecl that needs to be flattened.
   *  @return the same ConstDecl, but with the Expr part flattened.
   */
  public Object visitConstDecl(ConstDecl constDecl)
  {
    DeclName decl = constDecl.getDeclName();
    Expr expr = constDecl.getExpr();
    RefName eresult = (RefName)expr.accept(this);  // recursive flatten
    // we have to wrap a RefExpr around eresult, so it has the right type.
    RefExpr refexpr = zlive_.getFactory().createRefExpr(eresult);
    return zlive_.getFactory().createConstDecl(decl,refexpr);
  }

/*
  public Object visitFreetype(Freetype zedObject) { return zedObject; }
  public Object visitNameNamePair(NameNamePair zedObject) {return zedObject; }
  public Object visitLetExpr(LetExpr zedObject) {return zedObject; }
  public Object visitSignature(Signature zedObject) {return zedObject; }
  public Object visitProdType(ProdType zedObject) {return zedObject; }
  public Object visitDecl(Decl zedObject) {return zedObject; }
  public Object visitImpliesExpr(ImpliesExpr zedObject) {return zedObject; }
  public Object visitMuExpr(MuExpr zedObject) {return zedObject; }
  public Object visitSchExpr2(SchExpr2 zedObject) {return zedObject; }
  public Object visitExistsExpr(ExistsExpr zedObject) {return zedObject; }
  public Object visitExists1Expr(Exists1Expr zedObject) {return zedObject; }
  public Object visitForallExpr(ForallExpr zedObject) {return zedObject; }
  public Object visitVarDecl(VarDecl zedObject) {return zedObject; }
  public Object visitCompExpr(CompExpr zedObject) {return zedObject; }
  public Object visitCondExpr(CondExpr zedObject) {return zedObject; }
  public Object visitLambdaExpr(LambdaExpr zedObject) {return zedObject; }
  public Object visitIffExpr(IffExpr zedObject) {return zedObject; }
  public Object visitQntExpr(QntExpr zedObject) {return zedObject; }
  public Object visitNameTypePair(NameTypePair zedObject) {return zedObject; }
  public Object visitSchText(SchText zedObject) {return zedObject; }
  public Object visitQnt1Expr(Qnt1Expr zedObject) {return zedObject; }
  public Object visitOperand(Operand zedObject) {return zedObject; }
  public Object visitProjExpr(ProjExpr zedObject) {return zedObject; }
  public Object visitBranch(Branch zedObject) {return zedObject; }
  public Object visitGenType(GenType zedObject) {return zedObject; }
  public Object visitPreExpr(PreExpr zedObject) {return zedObject; }
  public Object visitExprPred(ExprPred zedObject) {return zedObject; }
  public Object visitGivenType(GivenType zedObject) {return zedObject; }
  public Object visitInclDecl(InclDecl zedObject) {return zedObject; }
  public Object visitPred(Pred zedObject) {return zedObject; }
  public Object visitSchemaType(SchemaType zedObject) {return zedObject; }
  public Object visitBindSelExpr(BindSelExpr zedObject) {return zedObject; }
  public Object visitDeclName(DeclName zedObject) {return zedObject; }
  public Object visitOrExpr(OrExpr zedObject) {return zedObject; }
  public Object visitSpec(Spec zedObject) {return zedObject; }
  public Object visitHideExpr(HideExpr zedObject) {return zedObject; }
  public Object visitPowerType(PowerType zedObject) {return zedObject; }
  public Object visitAndExpr(AndExpr zedObject) {return zedObject; }
  public Object visitRenameExpr(RenameExpr zedObject) {return zedObject; }
  public Object visitThetaExpr(ThetaExpr zedObject) {return zedObject; }
  public Object visitPipeExpr(PipeExpr zedObject) {return zedObject; }
  public Object visitNegExpr(NegExpr zedObject) {return zedObject; }
  public Object visitDecorExpr(DecorExpr zedObject) {return zedObject; }
  public Object visitExists1Pred(Exists1Pred zedObject) {return zedObject; }
  public Object visitSchExpr(SchExpr zedObject) {return zedObject; }
*/
}

