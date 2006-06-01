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

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.zpatt.ast.*;

public interface ProverProviso
  extends Proviso
{
  /** Checks the correctness of this proviso/sidecondition. 
   *  Before this check() method is called (for the first time), we say that
   *  the sequent has UNCHECKED status. After this check() method
   *  has been called, the sequent can be in one of three states: PASS (the
   *  side-condition was correctly discharged), FAIL (the side-condition is
   *  false), UNKNOWN (the side-condition needs to be checked later,
   *  when the sequent is instantiated more fully).
   *  
   * @param manager
   * @param section
   */
  void check(SectionManager manager, String section);
  Status getStatus();

  enum Status
  {
    FAIL,
    PASS,
    UNCHECKED,
    UNKNOWN;
  }
}
