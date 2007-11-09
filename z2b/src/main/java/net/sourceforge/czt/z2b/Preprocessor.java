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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

class Preprocessor
{
  private RuleTable rules_;
  private Factory factory_ = new Factory();

  Preprocessor()
    throws UnfoldException
  {
    try {
      SectionManager manager = new SectionManager("zpatt");
      rules_ = (RuleTable)
        manager.get(new Key("expansion_rules", RuleTable.class));
      RuleTable simplificationRules = (RuleTable)
        manager.get(new Key("simplification_rules", RuleTable.class));
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
      final List<Expr> exprList = new ArrayList<Expr>();
      final ZName name = factory_.createZName("normalize",
                                              factory_.createZStrokeList(),
                                              null);
      final ExprList refExprList = factory_.createZExprList();
      exprList.add(factory_.createRefExpr(name, refExprList, false, false));
      exprList.add(expr);
      final ApplExpr applExpr = factory_.createApplExpr(exprList, false);
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
