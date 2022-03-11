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
  private Map<String,RulePara> map_ = new HashMap<String,RulePara>();
  private List<RulePara> rules_ = new ArrayList<RulePara>();

  public void addRuleParas(RuleTable table)
    throws RuleTableException
  {
    addRuleParas(table.rules_);
  }

  public void addRuleParas(List<RulePara> rules)
    throws RuleTableException
  {
    for (RulePara rule : rules) {
      addRulePara(rule);
    }
  }

  public void addRulePara(RulePara rule)
    throws RuleTableException
  {
    final String rulename = rule.getName();
    RulePara alreadyIn = map_.get(rulename);
    if (alreadyIn != null && ! alreadyIn.equals(rule)) {
      final String message = "RulePara " + rulename + " defined twice";
      throw new RuleTableException(message);
    }
    rules_.add(rule);
    map_.put(rulename, rule);
  }

  public Iterator<RulePara> iterator()
  {
    return rules_.iterator();
  }

  /**
   * Convenience method for getRule.
   */
  public RulePara get(String name)
  {
    return getRulePara(name);
  }

  public RulePara getRulePara(String name)
  {
    return map_.get(name);
  }

  @Deprecated
  public Map<String,RulePara> getRuleParas()
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
    /**
	 * 
	 */
	private static final long serialVersionUID = -1694100700569618801L;

	public RuleTableException(String message)
    {
      super(message);
    }
  }
}
