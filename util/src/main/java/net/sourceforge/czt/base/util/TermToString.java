/*
  Copyright 2005, 2007 Mark Utting
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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;

/**
 * Converter from Term to String.  Usually used for debugging purposes.
 */
public class TermToString
  implements TermVisitor<Object>
{
  protected StringBuffer buffer_ = new StringBuffer();

  public String getString()
  {
    return buffer_.toString();
  }

  public void reset()
  {
    buffer_ = new StringBuffer();
  }

  public Object visitTerm(Term term)
  {
    buffer_.append(term.getClass().getSimpleName() + "( ");
    for (Object o : term.getChildren()) {
      if (o instanceof Term) {
        Term child = (Term) o;
        child.accept(this);
      }
      else {
        buffer_.append(o);
      }
      buffer_.append(" ");
    }
    buffer_.append(")");
    return null;
  }

  public static String apply(Term term)
  {
    TermToString visitor = new TermToString();
    term.accept(visitor);
    return visitor.getString();
  }
}
