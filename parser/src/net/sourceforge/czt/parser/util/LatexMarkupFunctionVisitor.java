/*
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

public class LatexMarkupFunctionVisitor
  implements TermVisitor,
             LatexMarkupParaVisitor,
             ListTermVisitor,
             ParaVisitor,
             ZSectVisitor
{
  private LatexMarkupFunction table_;
  private SectionInfo sectInfo_;
  private Set dependencies_;

  /**
   * Creates a new latex markup function visitor.
   * The section information should be able to provide information of type
   * <code>net.sourceforge.czt.parser.util.LatexMarkupFunction.class</code>.
   */
  public LatexMarkupFunctionVisitor(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public Class getInfoType()
  {
    return LatexMarkupFunction.class;
  }

  public Set getDependencies()
  {
    return dependencies_;
  }

  public Object run(ZSect sect)
  {
    sect.accept(this);
    return getLatexMarkupFunction();
  }

  public List getRequiredInfoTypes()
  {
    List result = new ArrayList();
    result.add(LatexMarkupFunction.class);
    return result;
  }

  public LatexMarkupFunction getLatexMarkupFunction()
  {
    return table_;
  }

  public Object visitTerm(Term term)
  {
    final String message =
      "LatexMarkupFunction can only be build for ZSects; " +
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

  public Object visitPara(Para para)
  {
    return null;
  }

  public Object visitLatexMarkupPara(LatexMarkupPara para)
  {
    List directives = para.getDirective();
    for (Iterator iter = directives.iterator(); iter.hasNext(); ) {
      Directive directive = (Directive) iter.next();
      try {
        table_.add(directive);
      }
      catch (MarkupException e)
      {
        throw new CztException(e);
      }
    }
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    table_ = new LatexMarkupFunction(name);
    for (Iterator iter = zSect.getParent().iterator(); iter.hasNext(); ) {
      Parent parent = (Parent) iter.next();
      LatexMarkupFunction parentTable =
        (LatexMarkupFunction) getInfo(parent.getWord(),
                                      LatexMarkupFunction.class);
      try {
        table_.add(parentTable);
      }
      catch (MarkupException e)
      {
        throw new CztException(e);
      }
    }
    visit(zSect.getPara());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }

  private Object getInfo(String name, Class type)
  {
    Key key = new Key(name, type);
    dependencies_.add(key);
    return sectInfo_.getInfo(name, OpTable.class);
  }
}
