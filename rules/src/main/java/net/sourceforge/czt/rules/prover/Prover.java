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

package net.sourceforge.czt.rules.prover;

import net.sourceforge.czt.zpatt.ast.Sequent;

/**
 * <p>A prover can be used to find proofs.</p>
 *
 * <p>Different provers might use different strategies to find proofs
 * (for example depth-first versus breadth-first search).</p>
 *
 * <p>This very first version does not support searching for
 * alternative proofs, nor does it support undos (reseting the
 * bindings after a proof has been found).  This needs updating!</p>
 *
 * @author Petra Malik
 */
public interface Prover
{
  /**
   * Proves a given sequent.  Returns <code>true</code> if a proof
   * has been found.  In this case, the Deduction element of the
   * given Sequent contains the proof.
   */
  boolean prove(Sequent conclusion);
}
