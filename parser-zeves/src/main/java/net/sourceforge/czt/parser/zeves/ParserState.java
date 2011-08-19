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
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;

import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;

/**
 *
 * @author Leo Freitas
 * @date Jul 4, 2011
 */
public class ParserState extends net.sourceforge.czt.parser.z.ParserState
{
  private List<Pair<Pred, ZEvesLabel>> labelledPreds_;
  private static int freshAxiomNo_ = 1;
  private final LabelCleaningVisitor labelCleaningVisitor_ ;

  private static final String AXIOM_LABEL_NAME = "axiom";

  public ParserState(Source loc)
  {
    super(loc);
    labelledPreds_ = new ArrayList<Pair<Pred, ZEvesLabel>>();
    labelCleaningVisitor_ = new LabelCleaningVisitor();
   // proofScripts_.reset();
  }

  public void storeZEvesLabelFor(Pred p, ZEvesLabel l)
  {
    labelledPreds_.add(new Pair<Pred, ZEvesLabel>(p, l));
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

  public void associateLabelsToPreds()
  {
    for(Pair<Pred, ZEvesLabel> pair : labelledPreds_)
    {
      pair.getFirst().getAnns().add(pair.getSecond());
    }
    clearLabelPredList();
  }

  public String freshLabelName()
  {
    final String result = AXIOM_LABEL_NAME + freshAxiomNo_;
    freshAxiomNo_++;
    return result;
  }

  @SuppressWarnings("FinalClass")
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
