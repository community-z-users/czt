/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.rules.rewriter;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprList;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.util.Factory;

/**
 * All section managers mentioned here must support Z Pattern.
 */
public class RewriteUtils
{
  /** Do not create instances of this class. */
  private RewriteUtils() {}
  private static Factory factory_ = new Factory();

  /**
   * Runs the rewriter (strategy innermost) for the given term.
   * The rules are taken from the given section.
   */
  public static Term rewrite(Term term, SectionManager manager, String section)
    throws CommandException, UnboundJokerException
  {
    RuleTable rules = 
      manager.get(new Key<RuleTable>(section, RuleTable.class));
    return Strategies.innermost(term, rules, manager, section);
  }

  public static ApplExpr createNormalizeAppl(Expr expr)
  {
//    final Factory factory = new Factory();
    final List<Expr> exprList = new ArrayList<Expr>();
    final Name name = factory_.createZName("normalize",
                                          factory_.createZStrokeList(),
                                          null);
    final ExprList refExprList = factory_.createZExprList();
    exprList.add(factory_.createRefExpr(name, refExprList, false, false));
    exprList.add(expr);
    return factory_.createApplExpr(exprList, false);
  }
}
