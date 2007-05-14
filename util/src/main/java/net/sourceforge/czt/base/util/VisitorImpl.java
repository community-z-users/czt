/*
  Copyright 2006, 2007 Mark Utting
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

package net.sourceforge.czt.base.util;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

/**
 * A helper visitor implementation.
 *
 * @param <R> the return type of the visit method.
 * @author Petra Malik
 */
public class VisitorImpl<R>
  implements Visitor<R>
{
  private Visit<R> visit_;

  public void setVisit(Visit<R> visit)
  {
    visit_ = visit;
  }

  public Visit<R> getVisit()
  {
    return visit_;
  }

  protected R visit(Term term)
  {
    if (visit_ != null) return visit_.visit(term);
    if (term != null) return term.accept(this);
    return null;
  }
}
