
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

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
package net.sourceforge.czt.core.ast;

import net.sourceforge.czt.zed.ast.*;

/**
 * A declaring name.
 *
 * @author Gnast version 0.1
 */
public interface DeclName extends Name
{

  /**
   * Returns the Id element.
   *
   * @return the Id element.
   */
  public String getId();

  /**
   * Sets the Id element.
   *
   * @param id   the Id element.
   * @see #getId
   */
  public void setId(String id);
}
