/*
  Copyright (C) 2009 Leo Freitas
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

public class ThmTableVisitor
  extends AbstractVisitor<Object>
  implements TermVisitor<Object>,
             ConjParaVisitor<Object>,
             ParaVisitor<Object>,
             ZParaListVisitor<Object>,
             ZSectVisitor<Object>
{
  private ThmTable table_;

  /**
   * Creates a new named conjecrure table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.ThmTable.class</code>.
   */
  public ThmTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Class<ThmTable> getInfoType()
  {
    return ThmTable.class;
  }

  public Object run(Term term)
    throws CommandException
  {
    super.run(term);
    return getThmTable();
  }

  protected ThmTable getThmTable()
  {
    return table_;
  }

  public Object visitTerm(Term term)
  {
    final String message = "ThmTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  public Object visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    try {
      table_.add(conjPara);
    }
    catch (ThmTable.ThmTableException e) {
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
    List<ThmTable> parentTables = new ArrayList<ThmTable>();
    for (Parent parent : zSect.getParent()) {
      ThmTable parentTable =
        (ThmTable) get(parent.getWord(), ThmTable.class);
      parentTables.add(parentTable);
    }
    try {
      table_ = new ThmTable(name, parentTables);
    }
    catch (InfoTable.InfoTableException e)
    {
      throw new CztException(e);
    }
    visit(zSect.getParaList());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }
}
