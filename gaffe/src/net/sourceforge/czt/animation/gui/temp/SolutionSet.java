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

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.Vector;

public class SolutionSet {
  private List/*<ZBinding>*/ solutions;
  private ListIterator currentSolution;
  public SolutionSet(Set/*<ZBinding>*/ solutions) {
    this.solutions=new Vector(solutions);
    currentSolution=this.solutions.listIterator();
  };
  public SolutionSet(ZBinding solution) {
    this.solutions=new Vector();
    this.solutions.add(solution);
    currentSolution=this.solutions.listIterator();
  };
  
  
  public ZBinding getCurrentSolution() {
    if(!currentSolution.hasNext()) return null;
    ZBinding current=(ZBinding)currentSolution.next();
    currentSolution.previous();
    return current;
  };
  public boolean hasCurrentSolution() {
    return currentSolution.hasNext();
  };
  public boolean hasNextSolution() {
    if(!hasCurrentSolution()) return false;
    currentSolution.next();
    boolean hasnext=currentSolution.hasNext();
    currentSolution.previous();
    return hasnext;    
  };
  public void nextSolution() {
    if(hasNextSolution()) {
      currentSolution.next();
      propertyChangeSupport.firePropertyChange("currentSolution",null,null);
    }
  };
  public boolean hasPreviousSolution() {
    return currentSolution.hasPrevious();
  };
  public void previousSolution() {
    if(hasPreviousSolution()) {
      currentSolution.previous();
      propertyChangeSupport.firePropertyChange("currentSolution",null,null);
    }
  };

  protected PropertyChangeSupport propertyChangeSupport=new PropertyChangeSupport(this);
  
  public void addPropertyChangeListener(PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(listener);
  };
  public void removePropertyChangeListener(PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(listener);
  };
  public PropertyChangeListener[] getPropertyChangeListeners() {
    return propertyChangeSupport.getPropertyChangeListeners();
  };
  public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(propertyName,listener);
  };
  public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
    propertyChangeSupport.removePropertyChangeListener(propertyName,listener);
  };
  public PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
    return propertyChangeSupport.getPropertyChangeListeners(propertyName);
  };
  public boolean hasListeners(String propertyName) {
    return propertyChangeSupport.hasListeners(propertyName);
  };

};
