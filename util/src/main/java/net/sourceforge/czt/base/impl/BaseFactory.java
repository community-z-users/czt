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

package net.sourceforge.czt.base.impl;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.Visit;
import net.sourceforge.czt.base.util.VisitorImpl;

/**
 * The base class of AST factories.
 */
public abstract class BaseFactory
{
  private VisitorImpl<String> toStringVisitor_;

  protected BaseFactory()
  {
    toStringVisitor_ = null;
  }

  /**
   * Sets the visit method of the given visitor to toString.
   */
  protected BaseFactory(VisitorImpl<String> toStringVisitor)
  {
    toStringVisitor_ = toStringVisitor;
    setVisitMethod();
  }

  private void setVisitMethod()
  {
    if (toStringVisitor_ != null) {
      Visit<String> visit = new Visit<String>()
        {
          public String visit(Term term)
          {
            if (term != null) return term.toString();
            return null;
          }
        };
      toStringVisitor_.setVisit(visit);
    }
  }

  public void setToStringVisitor(VisitorImpl<String> toStringVisitor,
                                 boolean setVisitMethod)
  {
    toStringVisitor_ = toStringVisitor;
    if (setVisitMethod) setVisitMethod();
  }

  public VisitorImpl<String> getToStringVisitor()
  {
    return toStringVisitor_;
  }

  public String toString(Term term)
  {
    return term.accept(toStringVisitor_);
  }
}
