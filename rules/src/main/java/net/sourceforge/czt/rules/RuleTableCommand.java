/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.rules;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zpatt.ast.RulePara;
import net.sourceforge.czt.zpatt.visitor.RuleParaVisitor;

public class RuleTableCommand
  implements Command
{
  @Override
  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    ZSect zSect = manager.get(new Key<ZSect>(name, ZSect.class));
    manager.endTransaction(new Key<RuleTable>(name, RuleTable.class), getRuleTable(zSect, manager));
    return true;
  }

  public static class RuleTableVisitor
    implements TermVisitor<Object>,
               SpecVisitor<Object>,
               ZParaListVisitor<Object>,
               ZSectVisitor<Object>,
               RuleParaVisitor<Object>
  {
    private final RuleTable rules_ = new RuleTable();
    private final SectionManager manager_;

    public RuleTableVisitor(SectionManager manager)
    {
      manager_ = manager;
    }

    public RuleTable getRuleTable()
    {
      return rules_;
    }

    @Override
    public Object visitTerm(Term term)
    {
      return null;
    }

    @Override
    public Object visitSpec(Spec spec)
    {
      for (Sect sect : spec.getSect()) {
        sect.accept(this);
      }
      return null;
    }

    @Override
    public Object visitZSect(ZSect zSect)
    {
      for (Parent p : zSect.getParent()) {
        try {
          RuleTable parentRuleTable =  manager_.get(new Key<RuleTable>(p.getWord(), RuleTable.class));
          rules_.addRuleParas(parentRuleTable);
        }
        catch (CommandException e) {
          System.err.println("Cannot get RuleTable for parent " + p.getWord());
        }
        catch (RuleTable.RuleTableException e) {
          throw new VisitorException(e);
        }
      }
      zSect.getParaList().accept(this);
      return null;
    }

    @Override
    public Object visitZParaList(ZParaList list)
    {
      for (Para para : list) {
        para.accept(this);
      }
      return null;
    }

    @Override
    public Object visitRulePara(RulePara rulePara)
    {
      try {
        rules_.addRulePara(rulePara);
      }
      catch (RuleTable.RuleTableException e) {
        throw new VisitorException(e);
      }
      return null;
    }
  }

  public static RuleTable getRuleTable(Term ast, SectionManager manager)
    throws CommandException
  {
    RuleTableVisitor visitor = new RuleTableVisitor(manager);
    try {
      ast.accept(visitor);
    }
    catch (VisitorException e) {
      throw new CommandException(manager.getDialect(), e.getCause());
    }
    return visitor.getRuleTable();
  }

  public static class VisitorException
    extends net.sourceforge.czt.util.CztException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -1958378042480636635L;

	public VisitorException(Exception cause)
    {
      super(cause);
    }
  }
}
