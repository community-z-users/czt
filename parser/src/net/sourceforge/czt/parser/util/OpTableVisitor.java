/*
  Copyright (C) 2004, 2005 Petra Malik
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

public class OpTableVisitor
  extends AbstractVisitor
  implements TermVisitor,
             ListTermVisitor,
             OptempParaVisitor,
             ParaVisitor,
             ZSectVisitor
{
  private OpTable table_;

  /**
   * Creates a new operator table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public OpTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Class getInfoType()
  {
    return OpTable.class;
  }

  public Object run(Term term)
    throws CommandException
  {
    super.run(term);
    return getOpTable();
  }

  protected OpTable getOpTable()
  {
    return table_;
  }

  public Object visitTerm(Term term)
  {
    final String message = "OpTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  public Object visitListTerm(ListTerm listTerm)
  {
    for (Iterator iter = listTerm.iterator(); iter.hasNext(); ) {
      Object o = iter.next();
      if (o instanceof Term) {
        Term t = (Term) o;
        visit(t);
      }
    }
    return null;
  }

  public Object visitOptempPara(OptempPara optempPara)
  {
    try {
      table_.add(optempPara);
    }
    catch (OpTable.OperatorException e) {
      throw new CztException(e);
    }
    return null;
  }

  public Object visitPara(Para para)
  {
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    List parentTables = new ArrayList();
    for (Iterator iter = zSect.getParent().iterator(); iter.hasNext(); ) {
      Parent parent = (Parent) iter.next();
      OpTable parentTable =
        (OpTable) get(parent.getWord(), OpTable.class);
      parentTables.add(parentTable);
    }
    try {
      table_ = new OpTable(name, parentTables);
    }
    catch (OpTable.OperatorException e)
    {
      throw new CztException(e);
    }
    visit(zSect.getPara());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }
}
