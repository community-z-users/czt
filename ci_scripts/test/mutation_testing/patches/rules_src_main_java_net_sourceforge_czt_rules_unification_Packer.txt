/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.rules.unification;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * A visitor that returns the necessary wrapper classes for terms.
 *
 * @author Petra Malik
 */
public class Packer
  implements HeadDeclListVisitor<Term>,
             TermVisitor<Term>,
             ZDeclListVisitor<Term>
{
  private final String DECLLIST = "DeclList";

  public Term visitTerm(Term term)
  {
    return term;
  }

  public Term visitHeadDeclList(HeadDeclList headDeclList)
  {
    return new HeadListWrapper(headDeclList, DECLLIST);
  }

  public Term visitZDeclList(ZDeclList zDeclList)
  {
    return new LispWrapper(zDeclList, DECLLIST);
  }
}
