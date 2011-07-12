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
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxSymbol;
import net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxSymbolVisitor;

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
    return (TypeChecker)typeChecker_;
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

  protected Name setCurrentProofName(Name name)
  {
    Name old = getTypeChecker().currentProofScript_;
    getTypeChecker().currentProofScript_ = name;
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
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
      sectName(), GlobalDefs.nearestLocAnn(term), markup());
    return errorAnn;
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
    for(ErrorAnn e : list)
    {
      error(term, e);
    }
  }

  /**
   * Method called for predicat type checking. It raises a warning if not solved in the second run.
   * @param term
   * @param pred
   */
  protected void typeCheckPred(Term term, Pred pred)
  {    
    UResult solved = pred.accept(predChecker());

    // if not solved in the first pass, do it again
    if (solved.equals(UResult.PARTIAL))
    {
      // try again - just like in Z
      solved = pred.accept(predChecker());
      
      // if not solved a second time, raise the warning 
      if (!solved.equals(UResult.SUCC))
      {
        warningManager().warn(term, WarningMessage.COULD_NOT_RESOLVE_PRED, 
          getConcreteSyntaxSymbol(term), term, pred);          
      }
    }
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
    if (errors().size() > 0) {      
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
}
