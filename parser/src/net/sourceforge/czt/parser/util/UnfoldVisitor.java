/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.parser.util;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class UnfoldVisitor
  implements TermVisitor,
             RefExprVisitor,
             ZSectVisitor
{
  DefinitionTable table_;
  OpTable opTable_;
  SectionInfo sectInfo_;

  /**
   * Creates a new flatten visitor.
   * The section information should be able to provide information of type
   * <code>net.sourceforge.czt.parser.util.OpInfo</code> and
   * <code>net.sourceforge.czt.parser.util.DefinitionTable</code>.
   */
  public UnfoldVisitor(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    DefinitionTable.Definition def =
      table_.lookup(refExpr.getRefName().toString());
    if (def != null && def.getDeclNames().size() == refExpr.getExpr().size()) {
      Expr newExpr = def.getExpr();
      if (def.getDeclNames().size() == 0) {
        return newExpr;
      }
    }
    return visitTerm(refExpr);
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    table_ = (DefinitionTable) sectInfo_.getInfo(name, DefinitionTable.class);
    //    opTable_ = (OpTable) sectInfo_.getInfo(name, OpTable.class);

    if (table_ == null /* || opTable_ == null */ ) {
      throw new CztException("Cannot get tables!");
    }
    return visitTerm(zSect);
  }
}

