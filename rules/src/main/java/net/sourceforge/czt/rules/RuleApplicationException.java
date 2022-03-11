/*
  Copyright (C) 2005, 2007 Petra Malik
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
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.ast.RulePara;

/**
 * Thrown when the application of a rule to a sequent has failed.
 */
public class RuleApplicationException
  extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -8156684409766561167L;
private RulePara rulePara_;
  private Sequent sequent_;

  public RuleApplicationException(RulePara rulePara,
                                  Sequent sequent,
                                  UnificationException cause)
  {
    super(cause);
    rulePara_ = rulePara;
    sequent_ = sequent;
  }

  public RulePara getRule()
  {
    return rulePara_;
  }

  public Sequent getSequent()
  {
    return sequent_;
  }

  public String getMessage()
  {
    return rulePara_.getName() + " cannot be applied to " + sequent_;
  }
}
