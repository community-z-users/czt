/*
  Copyright (C) 2005 Petra Malik
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
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

public class JokerTableVisitor
  extends AbstractVisitor
  implements TermVisitor,
             ListTermVisitor,
             JokersVisitor,
             ParaVisitor,
             ZSectVisitor
{
  private JokerTable table_;

  /**
   * Creates a new joker table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.JokerTable.class</code>.
   */
  public JokerTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Class getInfoType()
  {
    return JokerTable.class;
  }

  public Object run(Term term)
    throws CommandException
  {
    super.run(term);
    return getJokerTable();
  }

  protected JokerTable getJokerTable()
  {
    return table_;
  }

  public Object visitTerm(Term term)
  {
    final String message = "JokerTables can only be build for ZSects; " +
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

  public Object visitJokers(Jokers jokers)
  {
    try {
      table_.add(jokers);
    }
    catch (JokerTable.JokerException e) {
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
      JokerTable parentTable =
        (JokerTable) get(parent.getWord(), JokerTable.class);
      if (parentTable != null) {
        parentTables.add(parentTable);
      }
    }
    try {
      table_ = new JokerTable(name, parentTables);
    }
    catch (JokerTable.JokerException e)
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
