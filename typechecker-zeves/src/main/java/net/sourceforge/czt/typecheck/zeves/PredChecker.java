/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.typecheck.zeves;

import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.util.ZEvesUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 9, 2011
 */
public class PredChecker
        extends Checker<UResult>
        implements
            // AndPredVisitor<UResult>,
            //QntPredVisitor<UResult>,
            //ExprPredVisitor<UResult>,
            PredVisitor<UResult>
{

  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.PredChecker zPredChecker_;

  protected List<Pair<Pred, ZEvesLabel>> labelledPreds_;

  public PredChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPredChecker_ = new net.sourceforge.czt.typecheck.z.PredChecker(typeChecker);
    labelledPreds_ = new ArrayList<Pair<Pred, ZEvesLabel>>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }

  protected void clearLabelledPredList()
  {
    labelledPreds_.clear();
  }

  protected List<NameTypePair> getLabelledPredsSignature()
  {
    List<NameTypePair> result = factory().list();
    for (Pair<Pred, ZEvesLabel> pair : labelledPreds_)
    {
      // create a name type pair, where the type is an empty proof command info list
      result.add(factory().createNameTypePair(
              pair.getSecond().getName(),
              factory().getZEvesFactory().createProofType(
              factory().getZEvesFactory().createProofCommandInfoList(factory().<ProofCommandInfo>list()))));
    }
    clearLabelledPredList();
    return result;
  }

  protected void processZLabel(Pred term)
  {
    ZEvesLabel label = ZEvesUtils.getLabel(term);
    if (label != null)
    {
      // add a type id to this label name
      factory().addNameID(label.getName());
      labelledPreds_.add(Pair.getPair(term, label));
    }
  }

  protected UResult considerUndeclaredNamesFor(Pred term)
  {
    boolean ignoreNames = ignoreUndeclaredNames();
    if (ignoreNames)
      enterPredWithinConjParaScope();
    checkIfNeedIgnoreUndeclNameTag(term);
    UResult result = term.accept(zPredChecker_);
    if (ignoreNames)
      exitPredWithinConjParaScope();
    return result;
  }

  /**
   * ZEves actually allows undeclared names in any pred within ConjPara, not just
   * QntPred or ExprPred
   * @param term
   * @return
   */
  @Override
  public UResult visitPred(Pred term)
  {
    processZLabel(term);
    UResult result = considerUndeclaredNamesFor(term);
    //return term.accept(zPredChecker_);
    return result;
  }

  /**
   * Quantified predicates within ConjPara (e.g., ignoreUndeclaredNames() flag)
   * need to consider certain names as wildcards. This is shared between here and
   * SchTextChecker (see visitZSchText there for details).
   * @param term
   * @return
   */
//  @Override
//  public UResult visitQntPred(QntPred term)
//  {
//    processZLabel(term);
//    UResult result = considerUndeclaredNamesFor(term);
//    return result;
//  }

  /**
   * Another case where names are implicitly in context is schemas as predicates.
   * So for instance a theorem like
   *
   * \begin{theorem}{test}
   *    S \iff T
   * \end{theorem}
   *
   * where all variables of S and T are implicitly universally quantified.
   *
   * @param term
   * @return
   */
//  @Override
//  public UResult visitExprPred(ExprPred term)
//  {
//    // check for labels - unlikely
//    processZLabel(term);
//
//    // check if need to add IgnoreUndeclaredErrAnn to this term
//    // likely to be true: within a ConjPara, a schema set of names is to be treated differently
//    UResult result = considerUndeclaredNamesFor(term);
//    return result;
//  }

//  @Override
//  public UResult visitAndPred(AndPred term)
//  {
//     only NL/Semi And have multiple lables
//    if (term.getAnd().equals(And.NL) || term.getAnd().equals(And.Semi))
//    {
//      Pred leftP  = term.getLeftPred();
//      Pred rightP = term.getRightPred();
//
//       this will call visitPred within this checker (!)
//      UResult lR = leftP.accept(predChecker());
//      UResult rR = rightP.accept(predChecker());
//
//      ZEvesLabel label = ZEvesUtils.getLabel(term);
//
//       just like
//      UResult left = term.getLeftPred().accept(predChecker());
//      UResult right = term.getRightPred().accept(predChecker());
//      return UResult.conj(left, right);
//    }
//    else
//      return visitPred(term);
//  }
}
