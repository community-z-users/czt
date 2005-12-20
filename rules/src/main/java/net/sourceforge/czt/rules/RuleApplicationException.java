/*
  Copyright (C) 2005 Petra Malik
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

import net.sourceforge.czt.rules.unification.UnificationException;
import net.sourceforge.czt.zpatt.ast.PredSequent;
import net.sourceforge.czt.zpatt.ast.Rule;

/**
 * Thrown when the application of a rule to a sequent has failed.
 */
public class RuleApplicationException
  extends Exception
{
  private Rule rule_;
  private PredSequent sequent_;

  public RuleApplicationException(Rule rule,
                                  PredSequent sequent,
                                  UnificationException cause)
  {
    super(cause);
    rule_ = rule;
    sequent_ = sequent;
  }

  public Rule getRule()
  {
    return rule_;
  }

  public PredSequent getSequent()
  {
    return sequent_;
  }

  public String getMessage()
  {
    return rule_.getName() + " cannot be applied to " + sequent_;
  }
}
