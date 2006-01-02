/**
Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.modeljunit;

/** A transition represents a triple (StartState,Action,EndState). */
public class Transition
{
  private /*@non_null@*/ Object startState_;
  private /*@non_null@*/ String action_;
  private /*@non_null@*/ Object endState_;

  public Transition(/*@non_null@*/Object start, 
                    /*@non_null@*/String action,
                    /*@non_null@*/Object end)
  {
    startState_ = start;
    action_ = action;
    endState_ = end;
  }

  public Object getStartState()
  {
    return startState_;
  }

  public String getAction()
  {
    return action_;
  }

  public Object getEndState()
  {
    return endState_;
  }

  @Override
  public int hashCode()
  {
    return startState_.hashCode() ^ action_.hashCode() ^ endState_.hashCode();
  }

  @Override
  public boolean equals(Object other)
  {
    if (other instanceof Transition) {
      Transition tr = (Transition) other;
      return tr.startState_.equals(startState_)
        && tr.action_.equals(action_)
        && tr.endState_.equals(endState_);
    }
    return false;
  }
  
  @Override
  public String toString()
  {
    return "(" + startState_.toString() + ", "
           + action_.toString() + ", "
           + endState_.toString() + ")";
  }
}
