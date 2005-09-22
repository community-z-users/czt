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

import java.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** A subclass of Mode that records modes for compound structures.
 *  In addition to the usual mode information, it records a list
 *  of Mode objects for the subcomponents of the main flatpred object.
 *  For example, this is used to record the modes of the schema text
 *  and body of a universal quantifier.
 *
 *  @czt.todo: decide what the inputs of a compound mode should be.
 */
public class ModeList extends Mode
{
  private List<Mode> subModes_;
  
  /** Constructor for ModeList objects.
   */
  //@ requires solns > 0.0;
  public ModeList(/*@non_null@*/Envir postEnvir,
		  /*@non_null@*/BitSet inputs,
		  double solns,
		  /*@non_null@*/List<Mode> subModes)
  {
    super(postEnvir,inputs,solns);
    subModes_ = subModes;
  }

  /** A copy constructor. */
  public ModeList(/*@non_null@*/Mode mode)
  {
    this(mode.postEnvir_, mode.inputs_, mode.solutions_,
	 new ArrayList<Mode>());
  }

  /** Add a mode to the end of the submodes list.
   */
  public void add(/*@non_null@*/Mode mode)
  {
    subModes_.add(mode);
  }

  /** An iterator over the submodes list.
   *  These are the Mode objects for the subcomponents
   *  of the flatpred object associated with this mode.
   */
  public Iterator<Mode> iterator()
  { return subModes_.iterator(); }
}
