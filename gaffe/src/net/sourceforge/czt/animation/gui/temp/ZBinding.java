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
import java.util.Map;
import java.util.Set;

public class ZBinding implements ZValue{
  private Map/*<String,ZValue>*/ binding;
  public ZBinding() {
    this.binding=new HashMap();
  };
  public ZBinding(Map/*<String,ZValue>*/ binding) {
    this.binding=new HashMap(binding);
  };
  
  public Set keySet() {return binding.keySet();};

  public ZValue get(String location) {
    return (ZValue)binding.get(location);
  };  
};
