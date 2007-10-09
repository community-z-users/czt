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

public class LatexMarkupFunctionVisitor
  implements TermVisitor,
             LatexMarkupParaVisitor,
             ParaVisitor,
             ZParaListVisitor,
             ZSectVisitor
{
  private LatexMarkupFunction table_;
  private SectionManager manager_;
  private Set dependencies_ = new HashSet();

  /**
   * Creates a new latex markup function visitor.
   * The section information should be able to provide information of type
   * <code>net.sourceforge.czt.parser.util.LatexMarkupFunction.class</code>.
   */
  public LatexMarkupFunctionVisitor(SectionManager manager)
  {
    manager_ = manager;
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
    throws CommandException
  {
    try {
      sect.accept(this);
    }
    catch (LatexMarkupException e) {
      throw new CommandException(e.getCause());
    }
    return getLatexMarkupFunction();
  }

  public List<Class> getRequiredInfoTypes()
  {
    List<Class> result = new ArrayList<Class>();
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

  public Object visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  public Object visitPara(Para para)
  {
    return null;
  }

  public Object visitLatexMarkupPara(LatexMarkupPara para)
  {
    List directives = para.getDirective();
    for (Directive d : para.getDirective()) {
      try {
        table_.add(d);
      }
      catch (MarkupException e)
      {
        throw new LatexMarkupException(e);
      }
    }
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    table_ = new LatexMarkupFunction(name);
    for (Parent parent : zSect.getParent()) {
      try {
        LatexMarkupFunction parentTable = (LatexMarkupFunction)
          manager_.get(new Key(parent.getWord(), LatexMarkupFunction.class));
        table_.add(parentTable);
      }
      catch (CommandException e)
      {
        throw new LatexMarkupException(e);
      }
      catch (MarkupException e)
      {
        throw new LatexMarkupException(e);
      }
    }
    visit(zSect.getParaList());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }

  private static class LatexMarkupException
    extends RuntimeException
  {
    private LatexMarkupException(Exception cause)
    {
      super(cause);
    }
  }
}
