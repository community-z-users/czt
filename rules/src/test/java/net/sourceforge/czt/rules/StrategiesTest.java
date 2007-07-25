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

package net.sourceforge.czt.rules;

import junit.framework.TestCase;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.parser.z.ParseUtils;

public class StrategiesTest
  extends TestCase
{
  public void testInnermost1()
    throws Exception
  {
    rewrite("false \\lor \\lnot \\lnot true", "true");
  }

  protected void rewrite(String pred1, String pred2)
    throws Exception
  {
    final String section = "standard\\_toolkit";
    SectionManager manager = new SectionManager("zpatt");
    RuleTable rules = (RuleTable)
      manager.get(new Key("simplification_rules", RuleTable.class));
    StringSource source = new StringSource(pred1);
    Term term = ParseUtils.parsePred(source, section, manager);
    Prover prover = new SimpleProver(rules, manager, "standard_toolkit");
    term = Strategies.innermost(term, new RewriteOnceVisitor(prover));
    source = new StringSource(pred2);
    Term expected = ParseUtils.parsePred(source, section, manager);
    assertEquals(expected, term);
  }
}
