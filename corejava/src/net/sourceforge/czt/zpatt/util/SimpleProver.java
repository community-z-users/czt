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

package net.sourceforge.czt.zpatt.util;

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.zpatt.ast.*;

public class SimpleProver
  implements Prover
{
  private List<Rule> rules_;

  public SimpleProver(List<Rule> rules)
  {
    rules_ = rules;
  }

  /**
   * Tries all known rules to prove the sequent.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(PredSequent predSequent)
  {
    for (Iterator<Rule> i = rules_.iterator(); i.hasNext(); ) {
      Rule rule = i.next();
      Deduction deduction =
        new DeductionImpl(rule, predSequent);
      if (prove(deduction)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Tries to prove a deduction by proving all its children.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(Deduction deduction)
  {
    while (deduction.isValid())
    {
      if (prove(deduction.children())) return true;
      deduction.next();
    }
    return false;
  }

  /**
   * Tries to prove an array of sequents.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   *
   * Only handles PredSequent so far.
   * Other sequents are assumed to be true.
   */
  public boolean prove(Sequent[] sequents)
  {
    for (int i = 0; i < sequents.length; i++) {
      if (sequents[i] instanceof PredSequent) {
        if (! prove((PredSequent) sequents[i])) return false;
      }
    }
    return true;
  }
}
