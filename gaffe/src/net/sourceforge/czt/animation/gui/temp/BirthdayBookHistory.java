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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import net.sourceforge.czt.animation.ZLocator;
import net.sourceforge.czt.animation.gui.history.BasicHistory;

public class BirthdayBookHistory extends BasicHistory {
  private static ZGiven ok=new ZGiven("ok");
  private static ZGiven already_known=new ZGiven("already_known");
  private static ZGiven not_known=new ZGiven("not_known");

  public BirthdayBookHistory() {
    super();
    Map newResultsM=new HashMap();
    newResultsM.put("birthday'",new ZSet());
    newResultsM.put("known'",new ZSet());
    solutionSets.add(new SolutionSet(new ZBinding(newResultsM)));
    currentSolution=solutionSets.listIterator();
    System.err.println("History initialised: ");
    System.err.println("Current SolutionSet: "+getCurrentSolutionSet());
    System.err.println("Current Solution: "+getCurrentSolution());    
  };
  public synchronized void activateSchema(String schemaName) {
    System.err.println("Schema activated: "+schemaName);
    System.err.println("Current SolutionSet: "+getCurrentSolutionSet());
    System.err.println("Current Solution: "+getCurrentSolution());
    System.err.println("Inputs:");
    for(Iterator i=inputs.keySet().iterator();i.hasNext();) {
      Object a=i.next();
      System.err.println("   "+a+"\t"+inputs.get(a));
    };
    
    ZBinding currentResults=getCurrentSolution();
    ZBinding newResults;
    Map newResultsM=new HashMap();
    final ZSet newBirthdays;
    final ZSet newKnown;    
    final ZGiven resultOutput;
    final ZSet currentBirthdays=(ZSet)currentResults.get("birthday'");
    final ZSet currentKnown=(ZSet)currentResults.get("known'");       
    if("RAddBirthday".equals(schemaName)) {
      final ZGiven nameInput=(ZGiven)inputs.get(ZLocator.fromString("name?"));
      final ZGiven dateInput=(ZGiven)inputs.get(ZLocator.fromString("date?"));
      System.err.println("+++++"+nameInput+"\t"+dateInput);
      if(currentKnown.contains(nameInput)) {
	newBirthdays=currentBirthdays;
	newKnown=currentKnown;
	resultOutput=already_known;
      } else {
	Set s=currentKnown.getSet();
	s.add(nameInput);
	newKnown=new ZSet(s);
	s=currentBirthdays.getSet();
	s.add(new ZTuple(nameInput,dateInput));
	newBirthdays=new ZSet(s);
	resultOutput=ok;
      }
    } else if("RFindBirthday".equals(schemaName)) {
      final ZGiven nameInput=(ZGiven)inputs.get(ZLocator.fromString("name?"));
      ZGiven dateOutput=(ZGiven)inputs.get(ZLocator.fromString("name?"));
      newBirthdays=currentBirthdays;newKnown=currentKnown;
      if(currentKnown.contains(nameInput)) {
	for(Iterator iter=currentBirthdays.iterator();iter.hasNext();) {
	  ZTuple t=(ZTuple)iter.next();
	  if(t.get(0).equals(nameInput)) {
	    dateOutput=(ZGiven)t.get(1);break;
	  }
	}
	resultOutput=ok;
      } else {
	dateOutput=null;
	resultOutput=not_known;
      };
      newResultsM.put("date!",dateOutput);
    } else if("RRemind".equals(schemaName)) {
      final ZGiven dateInput=(ZGiven)inputs.get(ZLocator.fromString("today?"));
      final ZSet namesOutput;
      newBirthdays=currentBirthdays;newKnown=currentKnown;
      resultOutput=ok;
      Set s=new HashSet();
      for(Iterator iter=currentBirthdays.iterator();iter.hasNext();) {
	ZTuple t=(ZTuple)iter.next();
	if(t.get(1).equals(dateInput))
	  s.add(t.get(0));
      };
      namesOutput=new ZSet(s);
      newResultsM.put("cards!",namesOutput);
    } else {
      throw new Error("Error: Tried to run schema that isn't in birthday book!");
    };
    newResultsM.put("birthday",currentBirthdays);
    newResultsM.put("birthday'",newBirthdays);
    newResultsM.put("known",currentKnown);
    newResultsM.put("known'",newKnown);
    newResultsM.put("result!",resultOutput);
    newResults=new ZBinding(newResultsM);
    SolutionSet newSolutionSet=new SolutionSet(newResults);
    solutionSets=new Vector(solutionSets.subList(0,currentSolution.nextIndex()+1));
    solutionSets.add(newSolutionSet);
    currentSolution=solutionSets.listIterator(solutionSets.size()-1);
    System.err.println("Schema completed: "+schemaName);
    propertyChangeSupport.firePropertyChange("currentSolutionSet",null,null);
    propertyChangeSupport.firePropertyChange("currentSolution",null,null);

  };
};
