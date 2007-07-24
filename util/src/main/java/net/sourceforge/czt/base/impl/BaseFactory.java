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
import net.sourceforge.czt.util.Visitor;

/**
 * The base class of AST factories.
 */
public abstract class BaseFactory
{
  private Visitor<String> toStringVisitor_;

  protected BaseFactory()
  {
    toStringVisitor_ = null;
  }

  /**
   * Sets the visit method of the given visitor to toString.
   */
  protected BaseFactory(Visitor<String> toStringVisitor)
  {
    toStringVisitor_ = toStringVisitor;
  }

  public void setToStringVisitor(Visitor<String> toStringVisitor)
  {
    toStringVisitor_ = toStringVisitor;
  }

  public Visitor<String> getToStringVisitor()
  {
    return toStringVisitor_;
  }

  public String toString(Term term)
  {
    return term.accept(toStringVisitor_);
  }
}
