/*
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.zed.ast;

import net.sourceforge.czt.util.Visitor;

/**
 * An abstract Z construct.
 *
 * @author Petra Malik
 */
public interface Term
{
  /**
   * Accepts a visitor.
   */
  public Object accept(Visitor v);

  /**
   * Returns an array of all the children.
   * The order of the children is the same as provided in the
   * corresponding create method in the object factory.
   */
  public Object[] getChildren();

  /**
   * Creates a new object of the implementing class
   * with the object in <code>args</code> as its children.
   * The order and type of the children is similar
   * to the one returned by {@link #getChildren}.
   */
  public Term create(Object[] args);
}
