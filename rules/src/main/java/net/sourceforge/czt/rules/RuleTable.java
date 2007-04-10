/*
  Copyright (C) 2005, 2007 Mark Utting
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

import net.sourceforge.czt.zpatt.ast.*;

public class RuleTable
{
  private Map<String, Rule> map_ = new HashMap();
  private List<Rule> rules_ = new ArrayList();

  public void addRules(RuleTable table)
    throws RuleTableException
  {
    addRules(table.rules_);
  }

  public void addRules(List<Rule> rules)
    throws RuleTableException
  {
    for (Rule rule : rules) {
      addRule(rule);
    }
  }

  public void addRule(Rule rule)
    throws RuleTableException
  {
    final String rulename = rule.getName();
    rules_.add(rule);
    if (map_.get(rulename) != null) {
      final String message = "Rule " + rulename + " defined twice";
      throw new RuleTableException(message);
    }
    map_.put(rulename, rule);
  }

  public Iterator<Rule> iterator()
  {
    return rules_.iterator();
  }

  /**
   * Convenience method for getRule.
   */
  public Rule get(String rulename)
  {
    return getRule(rulename);
  }

  public Rule getRule(String name)
  {
    return map_.get(name);
  }

  @Deprecated
  public Map<String,Rule> getRules()
  {
    return map_;
  }

  public String toString()
  {
    return map_.toString();
  }

  public static class RuleTableException
    extends Exception
  {
    public RuleTableException(String message)
    {
      super(message);
    }
  }
}
