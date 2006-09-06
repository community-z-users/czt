/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.flatpred;

import net.sourceforge.czt.z.ast.Expr;

/** Stores the values for one startEval transition within FlatPredModel.
 *  The values must be in the same order as the free variables of
 *  the FlatPred being tested.  The startEval transition will put
 *  some of these values into the environment (the modes_ string
 *  determines which ones are compulsory), then call startEvaluation()
 *  and check that nextEvaluation returns true successes times.
 *  If successes==1, then it will also check that the values
 *  calculated by nextEvalution are the same as the values in args.
 *  
 * @author marku
 */
public class Eval
{
  public static final int UNDEF = -1;

  /** The number of times that this evaluation should succeed.
   *  UNDEF means that it should throw an UndefException.
   */
  public int successes;

  /** Which evaluation modes are allowed.
   *  This must be a string of 'I', 'O' and '?' characters.
   *  'I' means "Must be an input" and 'O' means "Must be an output",
   *  while '?' means "Input or Output".
   */
  public String modes;
  
  /** The values to be used during the evaluation. */
  public Expr[] args;
  
  public Eval(int numSuccesses, String modeMask, Expr... argValues)
  {
    assert modeMask != null;
    assert modeMask.length() == argValues.length;
    successes = numSuccesses;
    modes = modeMask;
    args = argValues;
  }
}
