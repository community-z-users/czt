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
package net.sourceforge.czt.animation;

import net.sourceforge.czt.animation.gui.temp.*;

/**
 * <code>ZLocator</code> for <code>ZBinding</code>s.
 * Locates a value inside a ZBinding.
 */
class  ZBindingLocator extends ZLocator {
  /**
   * The name of the variable in a binding to return.
   */
  protected String location;

  /**
   * Creates a ZBindingLocator for a variable named l.
   */
  public ZBindingLocator(String l) {
    location=l;
  };
  /**
   * Creates a ZBindingLocator for a variable <code>l</code>, with a locator <code>nl</code> to go
   * inside that variable.
   */
  public ZBindingLocator(String l, ZLocator nl) {
    super(nl);
    location=l;
  };
  /**
   * Locates a value within a ZBinding.  
   * @throws ClassCastException If the value passed wasn't a Binding, or if the next locator didn't match up with its variable.
   */
  public ZValue apply(ZValue v) throws ClassCastException{
    ZBinding t=(ZBinding) v;
    return recurse(t.get(location));
  };
};
