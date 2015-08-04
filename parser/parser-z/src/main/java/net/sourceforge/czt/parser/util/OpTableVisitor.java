/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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
  extends AbstractVisitor<OpTable>
  implements TermVisitor<OpTable>,
             OptempParaVisitor<OpTable>,
             ParaVisitor<OpTable>,
             ZParaListVisitor<OpTable>,
             ZSectVisitor<OpTable>
{
  private OpTable table_;

  /**
   * Creates a new operator table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   * @param sectInfo
   */
  public OpTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Class<OpTable> getInfoType()
  {
    return OpTable.class;
  }

  @Override
  public OpTable run(Term term)
    throws CommandException
  {
    super.run(term);
    return getOpTable();
  }

  protected OpTable getOpTable()
  {
    return table_;
  }

  @Override
  public OpTable visitTerm(Term term)
  {
    final String message = "OpTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  @Override
  public OpTable visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  @Override
  public OpTable visitOptempPara(OptempPara optempPara)
  {
	if (table_ == null) {
		throw new CztException(new OpTable.OperatorException(getSectionInfo().getDialect(), "Invalid table; not yet loaded through visitZSect"));
	}
    try {
      table_.add(optempPara);
    }
    catch (OpTable.OperatorException e) {
      throw new CztException(e);
    }
    return null;
  }

  @Override
  public OpTable visitPara(Para para)
  {
    return null;
  }

  @Override
  public OpTable visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    // TODO check for cyclic relationships?
    List<OpTable> parentTables = new ArrayList<OpTable>(zSect.getParent().size());
    for (Parent parent : zSect.getParent()) {
      OpTable parentTable =
        get(parent.getWord(), OpTable.class);
      parentTables.add(parentTable);
    }
    table_ = new OpTable(getSectionInfo().getDialect(), name);
    try {
      table_.addParents(parentTables);
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
