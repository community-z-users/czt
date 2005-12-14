/*
  Copyright (C) 2005 Mark Utting
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
  private Map<String, Rule> rules_ = new HashMap(); 

  public RuleTable(Map<String, Rule> rules)
  {
    rules_ = rules;
  }

  public Iterator<Rule> iterator()
  {
    return rules_.values().iterator();
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
    return rules_.get(name);
  }

  @Deprecated
  public Map<String,Rule> getRules()
  {
    return rules_;
  }

  public String toString()
  {
    return rules_.toString();
  }
}
