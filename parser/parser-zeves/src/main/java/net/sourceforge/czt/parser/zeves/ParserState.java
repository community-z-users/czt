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

package net.sourceforge.czt.parser.zeves;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;

import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.util.Factory;

/**
 *
 * @author Leo Freitas
 * @date Jul 4, 2011
 */
public class ParserState extends net.sourceforge.czt.parser.z.ParserState
{
  private List<Pair<Pred, ZEvesLabel>> labelledPreds_;
  private int freshAxiomNo_ = 1;
  //private final LabelCleaningVisitor labelCleaningVisitor_ ;
  //private final AxPara appliesToDef_;
  //private final OptempPara appliesToOpt_;

  private final Factory factory_ = new Factory();

  // "Axiom" to avoid problems with keyword "axiom"
  private static final String AXIOM_LABEL_NAME = "Axiom";

  public ParserState(Source loc)
  {
    super(loc);
    labelledPreds_ = new ArrayList<Pair<Pred, ZEvesLabel>>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

//  NOTE: added LatexMarkupDirective manually, and the other via zeves_toolkit as Tex source.
//
//    labelCleaningVisitor_ = new LabelCleaningVisitor();
//    %%Zinword applies\$to applies$to
//    Directive directive = factory_.createDirective("applies\\$to", "applies$to", DirectiveType.IN);
//    directive.getAnns().add(factory_.createLocAnn(location.getSource(),
//                                                  location.getLine(),
//                                                  null));
//    try {
//      markupFunction_.add(directive);
//    }
//    catch (MarkupException e) {
//      reportError(e);
//    }
//    \begin{zed}
//       \relation (\_ \appliesTo \_)
//    \end{zed}
//    appliesToOpt_ = factory_.createOptempPara();
//    appliesToOpt_.setCat(Cat.Relation);
//    appliesToOpt_.getOper().add(factory_.createOperand(Boolean.FALSE));
//    appliesToOpt_.getOper().add(factory_.createOperator("applies$to"));
//    appliesToOpt_.getOper().add(factory_.createOperand(Boolean.FALSE));
//     Don't use \rel to avoid dependency on set_toolkit.tex
//    \begin{gendef}[X, Y]
//       \_ ~applies\$to~ \_ : \power(\power~(X \cross Y) \cross X)
//    \where
//       \forall R: \power(X \cross Y); x: X @ R ~applies\$to~ x \iff (\exists_1 y: Y @ (x, y) \in R)
//    \end{gendef}
//    appliesToDef_ = factory_.createAxPara(
//            // [X, Y]
//            factory_.createZNameList(factory_.list(factory_.createZName("X"), factory_.createZName("Y"))),
//            factory_.createZSchText(
//              // \_ ~applies$to~ \_ : \power(\power(X \cross Y) \cross X)
//              factory_.createZDeclList(factory_.list(factory_.createVarDecl(
//                  factory_.createZNameList(factory_.list(factory_.createZName(ZString.ARG_TOK + "applies$to" + ZString.ARG_TOK))),
//                  factory_.createPowerExpr(factory_.createProdExpr(factory_.createPowerExpr(factory_.createProdExpr(
//                    factory_.createRefExpr(factory_.createZName("X")), factory_.createRefExpr(factory_.createZName("Y")))),
//                    factory_.createRefExpr(factory_.createZName("X"))))))),
//              // \forall R: \power~(X \cross Y); x : X @ ....
//              factory_.createForallPred(factory_.createZSchText(factory_.createZDeclList(factory_.list(
//                factory_.createVarDecl(factory_.createZNameList(factory_.list(factory_.createZName("R"))),
//                  factory_.createPowerExpr(factory_.createProdExpr(
//                    factory_.createRefExpr(factory_.createZName("X")), factory_.createRefExpr(factory_.createZName("Y"))))),
//                factory_.createVarDecl(factory_.createZNameList(factory_.list(factory_.createZName("x"))), factory_.createRefExpr(factory_.createZName("X"))))),
//                null),
//              factory_.createIffPred(
//                // (R, x) in _applies$to   =>  (R ~applies$to~ x)
//                factory_.createRelOpAppl(
//                  factory_.createTupleExpr(factory_.createRefExpr(factory_.createZName("R")), factory_.createRefExpr(factory_.createZName("x"))),
//                  factory_.createZName(ZString.ARG_TOK + "applies$to" + ZString.ARG_TOK)),
//                // (\exists_1 y: Y | null @ (x,y) \in R)
//                factory_.createExists1Pred(factory_.createZSchText(factory_.createZDeclList(factory_.list(
//                  factory_.createVarDecl(factory_.createZNameList(factory_.list(factory_.createZName("y"))), factory_.createRefExpr(factory_.createZName("Y"))))), null),
//                factory_.createSetMembership(
//                  factory_.createTupleExpr(factory_.createRefExpr(factory_.createZName("x")), factory_.createRefExpr(factory_.createZName("y"))),
//                  factory_.createRefExpr(factory_.createZName("R"))))))),
//            Box.AxBox);
  }

  protected void updateZSectWithAddedPara(ZSect sect)
  {
    //sect.getZParaList().add(0, appliesToOpt_);
    //sect.getZParaList().add(1, appliesToDef_);
  }

  public void storeZEvesLabelFor(Pred p, ZEvesLabel l)
  {
    labelledPreds_.add(Pair.getPair(p, l));
  }

  /**
   * Clears the labels with a schema predicates, added during "predicate"
   * parsing. It is not possible to have a separate "predicate" tree, given
   * its intricate relation with term/expression
   * @param term
   */
  public void clearLabelAssociations(Pred term)
  {
    //term.accept(labelCleaningVisitor_);
    clearLabelPredList();
  }

  public void clearLabelPredList()
  {
    labelledPreds_.clear();
  }

  protected List<? extends Pred> getTopLevelPred(Pred axParaPred)
  {
    List<Pred> result = factory_.list();
    if (axParaPred instanceof AndPred)
    {
      AndPred ap = (AndPred)axParaPred;
      for(Pred p : ap.getPred())
      {
        result.addAll(getTopLevelPred(p));
      }
    }
    else
    {
      result.add(axParaPred);
    }
    return result;
  }

  /**
   * The list of labelled preds might include more labels than needed because of
   * inner predicates like in (\IF Pred \THEN X \ELSE Y) (e.g., one label for the
   * whole if, and one for the Pred within its test.
   * This happens because we cannot have separate predicate parsing trees. we filter
   * those ineffective labels here.
   * @param axParaPred
   */
  public void associateLabelsToPreds(Pred axParaPred)
  {
    List<? extends Pred> topLevelPred = getTopLevelPred(axParaPred);
    for(Pair<Pred, ZEvesLabel> pair : labelledPreds_)
    {
      Pred p = pair.getFirst();
      if (topLevelPred.contains(p))
        p.getAnns().add(pair.getSecond());
    }
    clearLabelPredList();
  }

  public String freshLabelName()
  {
    final String result = AXIOM_LABEL_NAME + (getCurrentSectName() != null ? "_" + getCurrentSectName() : "") + freshAxiomNo_;
    //System.out.println("Creating default axiom label = " + result);
    freshAxiomNo_++;
    return result;
  }

  final class LabelCleaningVisitor implements TermVisitor<Object>
  {

    private void removeLabel(Term term)
    {
      for (Iterator<Object> iter = term.getAnns().iterator(); iter.hasNext(); )
      {
        Object ann = iter.next();
        if (ann instanceof ZEvesLabel)
        {
          iter.remove();
        }
      }
    }

    @Override
    public Object visitTerm(Term term)
    {
      removeLabel(term);
      VisitorUtils.visitTerm(this, term);
      return null;
    }
  }
}
