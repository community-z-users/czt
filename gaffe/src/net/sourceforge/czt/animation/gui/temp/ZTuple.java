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

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

public class ZTuple implements ZValue{
  private Vector tuple;
  public ZTuple() {
    this.tuple=new Vector();
  };
  public ZTuple(ZValue a, ZValue b) {
    tuple=new Vector();
    tuple.add(a);
    tuple.add(b);
  };
  public ZTuple(List/*<ZValue>*/ tuple) {
    this.tuple=new Vector(tuple);
  };
  
  public Iterator iterator() {return tuple.iterator();};
  public int size() {return tuple.size();};
  public ZValue get(int index) {return (ZValue)tuple.get(index);};
  
  public String toString() {
    String result = "( ";
    Iterator it=iterator();
    if(it.hasNext()) result+=it.next();
    while(it.hasNext()) result+=" , "+it.next();
    result+=" )";
    return result;
  };

  public boolean equals(Object obj) {
    return obj instanceof ZTuple && ((ZTuple)obj).tuple.equals(tuple);
  };
  public int hashCode() {
    return tuple.hashCode();
  };
};
