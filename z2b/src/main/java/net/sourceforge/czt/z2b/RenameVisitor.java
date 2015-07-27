/**
Copyright 2003, 2006 Mark Utting
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
package net.sourceforge.czt.z2b;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.*;


/**
 * This class renames a given set of names.
 * It is a simple syntactic transformation, done everywhere
 * in the given term, without regard to bound variables etc.
 *
 * @author Mark Utting
 */
public class RenameVisitor
  implements TermVisitor<Term>, NameVisitor<Term>
{
  Map<String,ZName> subs_;
  
  /**
   * Constructor for RenameVisitor
   *
   * @param rename  The map from old names to new names.
   */
  public RenameVisitor(Map<String,ZName> rename) {
    subs_ = rename;
  }

  /**
   * Apply this renaming to a Z term.
   * @param t  The original term.
   * @return   The substituted term.
   */
  public Term rename(Term t) {
    return t.accept(this);
  }

  /** This generic visit method recurses into all Z terms. */
  public Term visitTerm(Term term) {
    return VisitorUtils.visitTerm(this, term, true); 
  }

  /** This visit method performs the renaming. */
  public Term visitName(Name name)
  {
    String strName = name.accept(new PrintVisitor());
    if (subs_.containsKey(strName)) {
      return subs_.get(strName);
    }
    else {
      return name;
    }
  }
}
