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

import net.sourceforge.czt.animation.gui.temp.ZTuple;
import net.sourceforge.czt.animation.gui.temp.ZValue;

/**
 * <code>ZLocator</code> for <code>ZTuple</code>s.
 * Locates a value inside a ZTuple.
 */
class ZTupleLocator extends ZLocator
{
  /**
   * The index of the tuple-member to return.
   */
  protected int location_;

  /**
   * Creates a ZTupleLocator for the <code>l</code>th member of a tuple.
   */
  public ZTupleLocator(int l)
  {
    location_ = l;
  };

  /**
   * Creates a ZTupleLocator for the <code>l</code>th member of a tuple, with a
   * locator <code>nl</code> to go inside that member.
   */
  public ZTupleLocator(int l, ZLocator nl)
  {
    super(nl);
    location_ = l;
  };

  /**
   * Locates a value within a ZTuple.
   * @throws ClassCastException If the value passed wasn't a Tuple, or if the
   * next locator didn't match up with its variable.
   */
  public ZValue apply(ZValue v) throws ClassCastException
  {
    ZTuple t = (ZTuple) v;
    return recurse(t.get(location_));
  };

  public boolean equals(Object obj)
  {
    if (!(obj instanceof ZTupleLocator))
      return false;
    ZTupleLocator loc = (ZTupleLocator) obj;
    if ((nextLocator_ == null) != (loc.nextLocator_ == null))
      return false;
    if (nextLocator_ != null && !nextLocator_.equals(loc.nextLocator_))
      return false;
    return loc.location_ == location_;
  };

  public int hashCode()
  {
    if (nextLocator_ == null)
      return location_;
    else
      return location_ + nextLocator_.hashCode();
  };

  public String toString()
  {
    if (nextLocator_ == null)
      return "" + location_;
    else
      return location_ + "." + nextLocator_;
  };
};
