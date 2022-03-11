/*
  Copyright (C) 2007 Mark Utting
  This file is part of the CZT project.

  The CZT project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z2b;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.rewriter.RewriteUtils;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.*;

class Preprocessor
{
  private RuleTable rules_;

  Preprocessor()
    throws UnfoldException
  {
    try {
      SectionManager manager = new SectionManager(Dialect.ZPATT);
      rules_ = 
        manager.get(new Key<RuleTable>(Section.EXPANSION_RULES.getName(), RuleTable.class));
      RuleTable simplificationRules = 
        manager.get(new Key<RuleTable>(Section.SIMPLIFICATION_RULES.getName(), RuleTable.class));
      rules_.addRuleParas(simplificationRules);
    }
    catch(CommandException e) {
      throw new UnfoldException(e);
    }
    catch (RuleTable.RuleTableException e) {
      throw new UnfoldException(e);
    }
  }

  Term unfold(Expr expr, String section, SectionManager manager)
  {
    try {
      Expr applExpr = RewriteUtils.createNormalizeAppl(expr);
      return Strategies.innermost(applExpr, rules_, manager, section);
    }
    catch (CommandException e) {
      throw new RuntimeException("Unfolding failed!", e);
    }
    catch (UnboundJokerException e) {
      throw new RuntimeException("Unfolding failed!", e);
    }
  }
}
