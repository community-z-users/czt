/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License as published
by the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.modeljunit;


/** A transition pair is a pair of transitions (incoming,outgoing).
 *  They have the property that
 *  incoming.getEndState().equals(outgoing.getStartState()).
 *  (The constructor checks this and will throw an 
 *  IllegalArgumentException if it is not true).
 *  
 * @author marku
 */
public class TransitionPair
{
  private /*@non_null@*/ Transition incoming_,outgoing_;
  
  public TransitionPair(/*@non_null@*/Transition in,
                        /*@non_null@*/Transition out)
  {
    if ( ! in.getEndState().equals(out.getStartState()))
      throw new IllegalArgumentException("Bad transition pair: "+in+","+out); 
    incoming_ = in;
    outgoing_ = out;
  }

  public /*@pure non_null@*/ Transition getIncoming()
  {
    return incoming_;
  }
  
  public /*@pure non_null@*/ Transition getOutgoing()
  {
    return outgoing_;
  }

  @Override
  public int hashCode()
  {
    return incoming_.hashCode() ^ outgoing_.hashCode();
  }

  @Override
  public boolean equals(Object other)
  {
    if (other instanceof TransitionPair) {
      TransitionPair p = (TransitionPair) other;
      return incoming_.equals(p.incoming_)
          && outgoing_.equals(p.outgoing_);
    }
    return false; 
  }

  @Override
  public String toString()
  {
    return incoming_.toString()+","+outgoing_.toString();
  }
}
