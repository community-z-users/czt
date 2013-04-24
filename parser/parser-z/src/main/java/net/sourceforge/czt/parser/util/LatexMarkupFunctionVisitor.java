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

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;


public class LatexMarkupFunctionVisitor
  extends AbstractVisitor<LatexMarkupFunction>
  implements TermVisitor<LatexMarkupFunction>,
             LatexMarkupParaVisitor<LatexMarkupFunction>,
             ParaVisitor<LatexMarkupFunction>,
             ZParaListVisitor<LatexMarkupFunction>,
             ZSectVisitor<LatexMarkupFunction>
{
  private LatexMarkupFunction table_;
  private final SectionManager hackPleaseDelete_;//TODO @czt.todo fix me

  /**
   * Creates a new latex markup function visitor.
   * The section information should be able to provide information of type
   * <code>net.sourceforge.czt.parser.util.LatexMarkupFunction.class</code>.
   * @param manager
   */
  public LatexMarkupFunctionVisitor(SectionManager manager)
  {
    super(manager);
    hackPleaseDelete_ = manager;
  }

  public LatexMarkupFunction run(ZSect sect)
    throws CommandException
  {
    try {
      sect.accept(this);
    }
    catch (LatexMarkupException e) {
      throw new CommandException(getSectionInfo().getDialect(), e.getCause());
    }
    return getLatexMarkupFunction();
  }

  public LatexMarkupFunction getLatexMarkupFunction()
  {
    return table_;
  }

  @Override
  public LatexMarkupFunction visitTerm(Term term)
  {
    final String message =
      "LatexMarkupFunction can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  @Override
  public LatexMarkupFunction visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  @Override
  public LatexMarkupFunction visitPara(Para para)
  {
    return null;
  }

  @Override
  public LatexMarkupFunction visitLatexMarkupPara(LatexMarkupPara para)
  {
    for (Directive d : para.getDirective()) {
      try {
        table_.add(getSectionInfo().getDialect(), d);
      }
      catch (MarkupException e)
      {
        throw new LatexMarkupException(e);
      }
    }
    return null;
  }

  @Override
  public LatexMarkupFunction visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    table_ = new LatexMarkupFunction(name);
    
    // use the cyclic manager to get valid parents avoiding cyclic recursion
    CyclicParseManager cyclicMan = CyclicParseManager.getManager(hackPleaseDelete_);
    List<Parent> validParents = cyclicMan.getValidParents(name, zSect.getParent()); 
    try {
      
      for (Parent parent : validParents) {
        
        try {
          LatexMarkupFunction parentTable = get(parent.getWord(), LatexMarkupFunction.class);
          table_.add(parentTable);
        }
        catch (CztException e)
        {
          if (e.getCause() instanceof CommandException)
          {
            throw new LatexMarkupException((CommandException)e.getCause());
          }
          else
          {
            throw e;
          }
        }
        catch (MarkupException e)
        {
          throw new LatexMarkupException(e);
        }
      }
      
    } finally {
      // mark section inactive
      cyclicMan.visitedParents(name);
    }
    
    visit(zSect.getParaList());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }

  private static class LatexMarkupException
    extends net.sourceforge.czt.util.CztException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -3780014359357207022L;

	private LatexMarkupException(Exception cause)
    {
      super(cause);
    }
  }
}
