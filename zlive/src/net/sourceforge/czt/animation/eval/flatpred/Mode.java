/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** A Mode object contains information about one way of executing a FlatPred.
    It contains statistics about the number of solutions expected when
    the FlatPred is executed, plus an updated environment which contains
    any variables created by the FlatPred.
 */
public class Mode
{
  /** Constructor for Mode objects. */
  //@ requires solns > 0.0;
  public Mode(/*@non_null@*/ Envir postEnv,
	      /*@non_null@*/ boolean[] inputs, double solns)
  {
    postEnvir_ = postEnv;
    solutions_ = solns;
    inputs_ = inputs;
  }

  /** The input/output directions of the mode.
      This is an array of booleans -- if the i'th entry is true
      then the i'th variable managed by this FlatPred is an input,
      otherwise it is an output.
  */
  protected /*@spec_public non_null@*/ boolean[] inputs_;

  /** The number of arguments managed by this Mode and FlatPred */
  public /*@pure@*/ int getNumArgs()
  { return inputs_.length; }

  /** Is the i'th argument an input. */
  //@ requires 0 <= argnum;
  //@ requires argnum < getNumArgs();
  public /*@pure@*/ boolean isInput(int argnum)
  { return inputs_[argnum]; }

  /** The expected number of solutions. */
  protected /*@spec_public@*/ double solutions_;
  //@ invariant solutions_ > 0.0;

  /** The environment after executing the FlatPred. */
  protected /*@spec_public@*/ Envir postEnvir_;

  /** The estimated number of solutions that the FlatPred will produce.
      The result will always be positive.  It is an approximation of how many 
      solutions the FlatPred is likely to generate in this mode.  
      For example, 1.0 means exactly one solution is expected, 100 means 
      that around 100 solutions are expected, and 0.5 means that 0 or 1 
      solutions are expected.
  */
  //@ requires true;
  //@ ensures \result == solutions_;
  public /*@pure@*/ double getSolutions()
  { return solutions_; }

  /** Get the environment that includes any output variables of FlatPred. */
  //@ requires true;
  //@ ensures \result == postEnvir_;
  public /*@pure@*/ Envir getEnvir()
  { return postEnvir_; }
}
