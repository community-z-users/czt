/*
Copyright (C) 2005, 2006, 2007, 2008 Leo Freitas
This file is part of the czt project.
The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.
The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.typecheck.zeves;

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.ThmTable;
import net.sourceforge.czt.parser.zeves.ProofTable;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxSymbol;
import net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxSymbolVisitor;
import net.sourceforge.czt.zeves.util.ZEvesUtils;

/**
 * Derived superclass of all XXXChecker classes (i.e., one for each syntactic 
 * category). It provides general facilities for the derived checkers. This 
 * usually includes typing environment lookup and update, factory methods,
 * syntax checks, and so on.
 *
 * @param <R> 
 * @author Leo Freitas
 */
public abstract class Checker<R>
        extends net.sourceforge.czt.typecheck.z.Checker<R>
{

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  protected Checker<ProofCommandInfo> proofCommandChecker()
  {
    return getTypeChecker().proofCommandChecker_;
  }

  /**
   * Overrides the default Z protocol to use the warning manager
   * @param term
   * @return
   */
  @Override
  public R visitTerm(Term term)
  {
    warningManager().warn(term, WarningMessage.UNKNOWN_TERM,
            this.getClass().getName(),
            getConcreteSyntaxSymbol(term));
    return null;
  }

  protected TypeChecker getTypeChecker()
  {
    return (TypeChecker) typeChecker_;
  }

  @Override
  protected net.sourceforge.czt.typecheck.zeves.impl.Factory factory()
  {
    return getTypeChecker().getFactory();
  }

  protected ZEvesConcreteSyntaxSymbolVisitor concreteSyntaxSymbolVisitor()
  {
    return getTypeChecker().concreteSyntaxSymbolVisitor_;
  }

  protected WarningManager warningManager()
  {
    return getTypeChecker().warningManager_;
  }

  @Override
  protected void setMarkup(Markup markup)
  {
    super.setMarkup(markup);
    warningManager().setMarkup(markup);
  }

  @Override
  protected void setSectName(String sectName)
  {
    super.setSectName(sectName);
    warningManager().setCurrentSectName(sectName);
  }

  /***********************************************************************
   * Methods for the various process related information 
   *********************************************************************
   * @return
   */
  protected Name getCurrentProofName()
  {
    return getTypeChecker().currentProofScript_;
  }

  protected String getCurrentThmName()
  {
    return getTypeChecker().currentThmName_;
  }

  protected void setCurrentThmName(String name)
  {
    getTypeChecker().currentThmName_ = name;
  }

  protected Name setCurrentProofName(Name name)
  {
    Name old = getTypeChecker().currentProofScript_;
    getTypeChecker().currentProofScript_ = name;
    return old;
  }

  protected Type getCurrentProofRefConjType()
  {
    return getTypeChecker().currentProofConjType_;
  }

  protected Type setCurrentProofRefConjType(Type type)
  {
    Type old = getTypeChecker().currentProofConjType_;
    getTypeChecker().currentProofConjType_ = type;
    return old;
  }

  protected ZEvesConcreteSyntaxSymbol getConcreteSyntaxSymbol(Term term)
  {
    return term.accept(concreteSyntaxSymbolVisitor());
  }

  protected Type getGlobalType(Name name)
  {
    return getGlobalType(ZUtils.assertZName(name));
  }

  protected Type getGlobalType(ZName name)
  {
    return getType(name);
  }

  protected ProofCommandInfo getPCI(ProofCommand term)
  {
    return term.getAnn(ProofCommandInfo.class);
  }

  protected static class IgnoreUndeclNameAnn {} //extends AnnImpl {}
  //protected static class IgnoreBindExprAnn {}

  protected boolean ignoreUndeclaredNames()
  {
    return getTypeChecker().ignoreUndeclaredNames_;
  }

  protected void setIgnoreUndeclaredNames(boolean v)
  {
    getTypeChecker().ignoreUndeclaredNames_ = v;
  }

  protected void enterPredWithinConjParaScope()
  {
    getTypeChecker().predWithinConjParaStack_.push(true);
  }

  protected void exitPredWithinConjParaScope()
  {
    getTypeChecker().predWithinConjParaStack_.pop();
  }

  protected boolean withinConjParaPredScope()
  {
    return !getTypeChecker().predWithinConjParaStack_.isEmpty();
  }

  /**
   * Since we do not yet have type information for Term, we need to guess if it
   * is a schema or not. Mostly always, it will be okay
   * @param term
   * @return
   */
  protected boolean isSchemaCalculusExpr(Term term)
  {
    boolean result = term instanceof Expr;
    if (result)
    {
      ZUtils.ZExprKind kind = ZUtils.whatKindOfZExpr((Expr)term);
      if (kind.equals(ZUtils.ZExprKind.MIXED) || kind.equals(ZUtils.ZExprKind.UNKNOWN))
      {
        warningManager().warn(term, WarningMessage.IGNORE_NAME_COMPLEX_SCHEMA_CALULUS_EXPR, getCurrentThmName(), term.getClass().getName());
      }
      result = kind.equals(ZUtils.ZExprKind.SCHEMA);
    }
    return result;
  }

//   ((term instanceof CondExpr) ||
//             (term instanceof LambdaExpr) ||
//             (term instanceof LetExpr) ||
//             (term instanceof MuExpr) ||
//             (term instanceof ApplExpr))


  protected boolean shouldIgnoreUndeclaredNamesIn(Term term)
  {
    return ((term instanceof RefExpr ||   // exprs: reference names, theta, sets;
            term instanceof ThetaExpr ||  // pred : schema calculus, MemPred
            term instanceof SetExpr ||
            term instanceof MemPred ||
            term instanceof ExprPred || 
            isSchemaCalculusExpr(term)) &&  // terms to consider
            withinConjParaPredScope());     // only those terms within ConjPara
  }

  @Override
  protected void checkSchTextPredPart(ZSchText zSchText)
  {
    super.checkSchTextPredPart(zSchText);
  }

  @Override
  protected List<NameTypePair> checkSchTextDeclPart(ZSchText zSchText)
  {
    return super.checkSchTextDeclPart(zSchText);
  }

  protected void checkIfNeedIgnoreUndeclNameTag(Term term)
  {
    // mark post check terms to ignore if term is of the right class
    // and the tagging flag is on
    if (ignoreUndeclaredNames() && shouldIgnoreUndeclaredNamesIn(term))
    {
      term.getAnns().add(new Checker.IgnoreUndeclNameAnn());
    }
  }

  // CHANGED UNIFICATION ALGO INSTEAD
//  protected void checkIfNeedBindTag(Term term)
//  {
//    // POWER BINDEXPR
//    if (term instanceof PowerExpr && ((PowerExpr) term).getExpr() instanceof BindExpr)
//    {
//      term.getAnns().add(new Checker.IgnoreBindExprAnn());
//    }
//    // BindExpr \pinj TYPE (e.g., RefExpr with
//    else if (term instanceof RefExpr)
//    {
//      ZExprList zel = ((RefExpr)term).getZExprList();
//      for (Expr e : zel.getExpr())
//      {
//        if (e instanceof BindExpr || (e instanceof PowerExpr && ((PowerExpr) e).getExpr() instanceof BindExpr))
//        {
//          term.getAnns().add(new Checker.IgnoreBindExprAnn());
//          break;
//        }
//      }
//    }
//    //if (term.hasAnn(Checker.IgnoreBindExprAnn.class))
//    //  System.out.println("checkIfNeedBindTag(" + term.getClass().getName() + ") = " + term.toString());
//  }

//  @Override
//  protected void addTermForPostChecking(Term term)
//  {
//    checkIfNeedIgnoreUndeclNameTag(term);
//    checkIfNeedBindTag(term);
//    super.addTermForPostChecking(term);
//  }

  protected void removeIgnoreAnn(Term term)
  {
    Checker.IgnoreUndeclNameAnn iuna = term.getAnn(Checker.IgnoreUndeclNameAnn.class);
    if (iuna!= null)
      term.getAnns().remove(iuna);
//    if (term.hasAnn(Checker.IgnoreBindExprAnn.class))
//      term.getAnns().remove(term.getAnn(Checker.IgnoreBindExprAnn.class));
  }

  @SuppressWarnings("unchecked")
  protected <T extends net.sourceforge.czt.typecheck.z.ErrorAnn> T updateErrorAnn(T error, Term term)
  {
    T result = error;
    // if there is a result that is about undeclared identifiers, and the term given
    // was tagged as one to ignore undeclared names with, then mark it as a warning.
    if (error != null)
    {
//      System.out.print("updateErrorAnn(" + error.getErrorMessage() + ", " + term.toString() + ") = ");
      // clear up the ann tag, if any
      if (term.hasAnn(Checker.IgnoreUndeclNameAnn.class))
      {
        if (error.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.UNDECLARED_IDENTIFIER.name()) ||
            error.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.UNDECLARED_IDENTIFIER_IN_EXPR.name()))
        {

  //      warningManager().warn(term, WarningMessage.UNDECLARED_NAME_ERROR_AS_WARNING, term.getClass().getName() + " = " + result.toString());
  //      result = null;//result.setErrorType(ErrorType.WARNING);
          final String errStr = error.toString();
          result = (T)errorAnn(term, ErrorMessage.UNDECLARED_NAME_ERROR_AS_WARNING, new Object[] { term.getClass().getName(), errStr });
          result.setErrorType(ErrorType.WARNING);
        }
        else if (error.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.TYPE_MISMATCH_IN_MEM_PRED.name()))
        {
          final String errStr = error.toString();
          result = (T)errorAnn(term, ErrorMessage.PRED_ERROR_AS_WARNING, new Object[] { term.getClass().getName(), errStr });
          result.setErrorType(ErrorType.WARNING);          
        }
      }
//      if (term.hasAnn(Checker.IgnoreBindExprAnn.class) &&
//          (error.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.NON_SET_IN_POWEREXPR.name()) ||
//           error.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.NON_SET_IN_INSTANTIATION.name())))
//      {
//        //System.out.println("updateErrorAnn(" + error.getErrorMessage() + ", " + term.toString() + ") = ");
//        final String errStr = error.toString();
//        result = (T)errorAnn(term, ErrorMessage.BINDEXPR_ERROR_AS_WARNING, new Object[] { term.getClass().getName(), errStr } );
//        result.setErrorType(ErrorType.WARNING);
//      }
//      System.out.println(result.getErrorMessage());// + ": " + error.toString());
    }

    return result;
  }

  protected void error(Term term, ErrorMessage errorMsg, Object... params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, errorMsg, params);
    error(term, errorAnn);
  }

  protected void error(Term term, ErrorMessage errorMsg, List<Object> params)
  {
    error(term, errorMsg, params.toArray());
  }

  
  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object... params)
  {
    return errorAnn(term, error.toString(), params);
  }

  @Override
  protected net.sourceforge.czt.typecheck.z.ErrorAnn errorAnn(Term term, net.sourceforge.czt.typecheck.z.ErrorMessage error, Object[] params)
  {
    net.sourceforge.czt.typecheck.z.ErrorAnn result = super.errorAnn(term, error, params);
    result = updateErrorAnn(result, term);
    return result;
  }
  
  @Override
  protected ErrorAnn errorAnn(Term term, String error, Object [] params)
  {
    // this method is very important to make sure the right "ErrorAnn" is created!
    ErrorAnn result = new ErrorAnn(error, params, sectInfo(),
      sectName(), GlobalDefs.nearestLocAnn(term),
      term, markup());
    result = updateErrorAnn(result, term);
    return result;
  }

  /**
   * Raise all the errors from the given list that were generated during 
   * the typechecking of the given term. This is to be called by all visiting
   * methods that used any of the general methods returning list of errors. 
   * This is important to avoid concurrent modification exceptions within 
   * the Z PostChecking protocol. 
   * 
   * @param term
   * @param list
   */
  protected void raiseErrors(Term term, List<ErrorAnn> list)
  {
    // raise all the errors from the list by adding them to the paraErrors()
    for (ErrorAnn e : list)
    {
      error(term, e);
    }
  }

  @Override
  protected SectTypeEnvAnn handleParentErrors(Parent parent, CommandException e)
  {
    if (e.getCause() instanceof TypeErrorException)
    {
      String parentName = parent.getWord();
    	
      List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> errors = ((TypeErrorException)e.getCause()).errors();
      int errorCnt = errors.size();
      WarningManager.WarningOutput wo = warningManager().getWarningOutput();
      // if we are to raise warnings, then don't consider what to disregard
      if (!wo.equals(WarningManager.WarningOutput.RAISE))
      {
        for(net.sourceforge.czt.typecheck.z.ErrorAnn error : errors)
        {
          // do not consider warnings as errors
          if (error.getErrorType().equals(ErrorType.WARNING))
          {
            errorCnt--;
            // perhaps show then if needed
            if (wo.equals(WarningManager.WarningOutput.SHOW))
              warningManager().warn(WarningMessage.PARENT_ERRORS_WARNING.getMessage(), 
            		  sectName(), parentName, error.toString());
          }
        }
      }
      if (errorCnt > 0)
      {
        int warningCnt = errors.size() - errorCnt;
        final String message = "Section " + sectName() + " contains " + errorCnt +
          (errorCnt == 1 ? " error" : " errors and ") + warningCnt +
          (warningCnt == 1 ? " warning " : " warnings ") + " from parent section " + parentName;
        Exception nestedException = new TypeErrorException(message, errors);
        return super.handleParentErrors(parent, new CommandException(getManager().getDialect(), nestedException));
      }
      else
      {
        // it should be already cached.
        try
        {
          return sectInfo().get(new Key<SectTypeEnvAnn>(parentName, SectTypeEnvAnn.class));
        }
        catch (CommandException f)
        {
          return super.handleParentErrors(parent, f);
        }
      }
    }
    else {
      return super.handleParentErrors(parent, e);
    }
  }

  /**
   * Method called for predicat type checking. It raises a warning if not solved in the second run.
   * @param term
   * @param pred
   */
  protected void typeCheckPred(Term term, Pred pred)
  {
    warningManager().warn(term, WarningMessage.IGNORE_PROOF_PRED, getCurrentProofName(), pred);
// IGNORE THIS BIT FOR NOW: later filter errors accordingly
//    List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> zGenOnly = factory().list(getTypeChecker().errors());
//    // TODO: there is more to it than just errors() (e.g., paraErrors() and undeclaredName()) - see clearErrors();
//
//    UResult solved = pred.accept(predChecker());
//
//    List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> zevesGenOnly = factory().list(getTypeChecker().errors());
//
//    // if not solved in the first pass, do it again
//    if (solved.equals(UResult.PARTIAL))
//    {
//      // try again - just like in Z
//      solved = pred.accept(predChecker());
//
//      // if not solved a second time, raise the warning
//      if (!solved.equals(UResult.SUCC))
//      {
//        warningManager().warn(term, WarningMessage.COULD_NOT_RESOLVE_PRED,
//                getConcreteSyntaxSymbol(term), term, pred);
//      }
//    }
  }

  protected void checkRefConjType(Term term, Term part, ErrorMessage msg, Type found)
  {
    if (found instanceof UnknownType) // or check to be !ProofType
    {
      //error(term, msg, getCurrentProofName(), part, found);
      //warningManager().warn(term, msg, getCurrentProofName(), part, found);
    }
  }

  protected Type typeCheckExpr(Term term, Expr expr, WarningMessage msg)
  {
    // IGNORE EXPR IN PROOFS FOR NOW!!!
    //warningManager().warn(term, WarningMessage.IGNORE_PROOF_EXPR, getCurrentProofName(), expr);
    //Type found = expr.accept(exprChecker());
    Type found = factory().createUnknownType();
    if (msg != null) // && some form of type unification here?
    {
      //warningManager().warn(term, msg, getCurrentProofName(), expr, found);
    }
    return found;
  }

  protected void typeCheckThmRef(Term term, Expr expr, ErrorMessage msg)
  {
    Type2 found = GlobalDefs.unwrapType(typeCheckExpr(term, expr, null));
    checkRefConjType(term, term, msg, found);
  }

  // Term = ProofCommand or ProofScript?
  protected Type2 typeCheckThmRef(Term term, Name name, ErrorMessage msg)
  {
    Type2 found = GlobalDefs.unwrapType(getType(name));
// z.ParaChecker.visitConjPara returns a ProdType with generics...
//  if (found instanceof ProdType)
    checkRefConjType(term, name, msg, found);
    return found;
  }

  @Override
  protected void addWarnings()
  {
    errors().addAll(warningManager().warnErrors());
    warningManager().clearWarnErrors();
  }

  @Override
  protected Boolean getResult()
  {
    Boolean result = Boolean.TRUE;
    // if there are errors, make sure warnings are not considered
    if (errors().size() > 0)
    {
      // if strict on warnings, then consider then as errors and return false
      result = !getTypeChecker().getWarningManager().getWarningOutput().equals(WarningManager.WarningOutput.RAISE);

      // otherwise, give the result without considering warnings
      if (result)
      {
        Iterator<net.sourceforge.czt.typecheck.z.ErrorAnn> it = errors().iterator();
        while (it.hasNext() && result)
        {
          net.sourceforge.czt.typecheck.z.ErrorAnn error = it.next();
          // do not consider warnings
          result = !error.getErrorType().equals(ErrorType.ERROR);
        }
        it = null;
      }
    }
    return result;
  }

  protected Signature wrapTypeAndAddAnn(Name declName, Type type, Para term)
  {
    NameTypePair pair = factory().createNameTypePair(declName, type);
    Signature result = factory().createSignature(factory().list(pair));
    addTypeAnn(term, type);
    return result;
  }

  protected void calculateTables(ZSect zSect)
  {
    try
    {
      getTypeChecker().thmTable_ = sectInfo().get(new Key<ThmTable>(zSect.getName(), ThmTable.class));
    }
    catch (CommandException ex)
    {
      warningManager().warn(zSect, WarningMessage.ZSECT_THMTBL_ERROR, zSect.getName());
    }
    try
    {
      getTypeChecker().proofTable_ = sectInfo().get(new Key<ProofTable>(zSect.getName(), ProofTable.class));
    }
    catch (CommandException ex)
    {
      warningManager().warn(zSect, WarningMessage.ZSECT_THMTBL_ERROR, zSect.getName());
    }
  }

  protected ThmTable getThmTable()
  {
    return getTypeChecker().thmTable_;
  }

  protected ProofTable getProofTable()
  {
    return getTypeChecker().proofTable_;
  }

    // allow for different kind of RenameExpr RenameList within
  @Override
  protected void addNameIDs(RenameExpr renameExpr)
  {
    if (renameExpr.getRenameList() instanceof InstantiationList)
      addNameIDs(ZEvesUtils.assertRenameListAsInstantiationList(renameExpr));
    else
      super.addNameIDs(renameExpr);
  }

  //add IDs to each new name in a list of renaming pairs
  protected void addNameIDs(InstantiationList instList)
  {
    for (Instantiation inst : instList)
    {
      // I am not sure about this! TODO: CHECK...
      // in ZRenameList, it is the getNewName() in NewOldPair
      if (inst.getExpr() instanceof RefExpr)
      {
        factory().addNameID(((RefExpr)inst.getExpr()).getName());
      }
    }
  }


}
