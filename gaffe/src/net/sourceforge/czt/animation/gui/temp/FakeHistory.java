/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
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
package net.sourceforge.czt.animation.gui.temp;

import net.sourceforge.czt.animation.gui.history.HistorySupport;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

/**
 * Fake History Interface that fakes interface with the animator.
 */
public class FakeHistory extends HistorySupport {
  
  private int currentPoint;
  private SolutionSet currentSolutionSet;
  private void setSolutionSet() {
    Map m=new HashMap();
    m.put("value",new ZNumber(currentPoint));
    Set s=new HashSet();
    s.add(new ZBinding(m));
    
    currentSolutionSet=new SolutionSet(s);
    
  };
  
  //Constructors
  public FakeHistory() {
    super();
    currentPoint=0;
    setSolutionSet();
  };


  //Functions from History
  public synchronized SolutionSet getCurrentSolutionSet() {
    return currentSolutionSet;
  };
  public synchronized void activateSchema(String schemaName) {
    super.activateSchema(schemaName);//XXX does nothing at the moment
  };


  //Methods for navigating through the solution sets.
  /**
   * @return true if there is another solution set after the current one.
   */
  public synchronized boolean hasNextSolutionSet() {
    return true;
  }
  /**
   * Moves to the next solution set
   */
  public synchronized void nextSolutionSet() {
    currentPoint++;
    setSolutionSet();
    propertyChangeSupport.firePropertyChange("currentSolutionSet",null,null);
    propertyChangeSupport.firePropertyChange("currentSolution",null,null);
  };
  /**
   * @return true if there is another solution set before the current one.
   */
  public synchronized boolean hasPreviousSolutionSet() {
    return currentPoint!=0;
  };
  /**
   * Moves to the previous solution set
   */
  public synchronized void previousSolutionSet() {
    if(currentPoint==0) return;
    currentPoint--;
    setSolutionSet();
    propertyChangeSupport.firePropertyChange("currentSolutionSet",null,null);
    propertyChangeSupport.firePropertyChange("currentSolution",null,null);
  };
};

