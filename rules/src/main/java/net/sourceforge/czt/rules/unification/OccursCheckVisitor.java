/*
  Copyright (C) 2006 Mark Utting
  This file is part of the CZT project.

  The CZT project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.rules.unification;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.rules.Joker;
import net.sourceforge.czt.util.Visitor;

/** Implements a simple occurs check, to avoid creating cyclic terms.
 *  The contains(term,joker) method is the main entry point.
 *  
 * @author marku
 */
public class OccursCheckVisitor
  implements Visitor<Boolean>,
             TermVisitor<Boolean>
{
  /** The Joker that we are looking for. */
  private Joker joker_;
  
  public OccursCheckVisitor()
  {
    VisitorUtils.checkVisitorRules(this);
  }

  /** True iff term contains joker.
   *  Note that jokers are assumed to be unique
   *  (ProverFactory ensures this), so the comparison
   *  with each subterm is done using ==.
   * @param term  Non-null term to check.
   * @param joker The joker to look for.
   * @return
   */
  public boolean contains(Term term, Joker joker)
  {
    joker_ = joker;
    return term.accept(this);
  }

  public Boolean visitTerm(Term term)
  {
    if (term == joker_)
      return Boolean.TRUE;
    if (term == null)
      return Boolean.FALSE;
    Object[] children = term.getChildren();
    for (Object t : children)
    {
      if (t instanceof Term && ((Term)t).accept(this).booleanValue())
        return Boolean.TRUE;
    }
    return Boolean.FALSE;
  }
}
