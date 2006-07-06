/*
  Copyright (C) 2005, 2006 Petra Malik
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

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

import net.sourceforge.czt.session.*;

public class RuleTableCommand
  implements Command
{
  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    ZSect zSect = (ZSect) manager.get(new Key(name, ZSect.class));
    manager.put(new Key(name, RuleTable.class), getRuleTable(zSect));
    return true;
  }

  public static class RuleTableVisitor
    implements TermVisitor,
               SpecVisitor,
               ZParaListVisitor,
               ZSectVisitor,
               RuleVisitor
  {
    private List<Rule> rules_ = new ArrayList<Rule>();

    public RuleTable getRuleTable()
    {
      return new RuleTable(rules_);
    }

    public Object visitTerm(Term term)
    {
      return null;
    }

    public Object visitSpec(Spec spec)
    {
      for (Sect sect : spec.getSect()) {
        sect.accept(this);
      }
      return null;
    }

    public Object visitZSect(ZSect zSect)
    {
      zSect.getParaList().accept(this);
      return null;
    }

    public Object visitZParaList(ZParaList list)
    {
      for (Para para : list) {
        para.accept(this);
      }
      return null;
    }

    public Object visitRule(Rule rule)
    {
      rules_.add(rule);
      return null;
    }
  }

  public static RuleTable getRuleTable(Term ast)
  {
    RuleTableVisitor visitor = new RuleTableVisitor();
    ast.accept(visitor);
    return visitor.getRuleTable();
  }
}
