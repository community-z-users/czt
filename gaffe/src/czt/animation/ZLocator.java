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
package czt.animation;

import czt.animation.gui.temp.*;

/**
 * General class for all locators.  Locates a value inside a composite ZValue (e.g. ZBinding, ZTuple).
 */
public abstract class ZLocator {
  /**
   * The next locator.  If this is not a multi-level locator, then <code>nextLocator</code> will be 
   * <code>null</code>.
   */
  protected ZLocator nextLocator;
  /**
   * Creates a single-level locator.
   */
  protected ZLocator() {
    nextLocator=null;
  };
  /**
   * Creates a multi-level locator.  Wraps another locator around nl.
   */
  protected ZLocator(ZLocator nl) {
    nextLocator=nl;
  };
  /**
   * Does the recursive part of an apply.
   */
  protected ZValue recurse(ZValue v) throws ClassCastException {
    return (nextLocator==null)?v:nextLocator.apply(v);
  };
  /**
   * Locates a value within <code>v</code>.
   * @throws ClassCastException If the value passed wasn't of the correct type for this locator, or if the next locator didn't match up with its variable.   */
  public abstract ZValue apply(ZValue v) throws ClassCastException;
};
