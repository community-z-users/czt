
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
package net.sourceforge.czt.z.ast;

import net.sourceforge.czt.base.ast.*;

/**
 * 
        A referencing name.
        The Decl attribute of type IDREF points to the matching declaration,
        which may not be the nearest enclosing one.
      
 *
 * @author Gnast version 0.1
 */
public interface RefName extends Name
{

  /**
   * Returns the Decl element.
   *
   * @return the Decl element.
   */
  DeclName getDecl();

  /**
   * Sets the Decl element.
   *
   * @param decl   the Decl element.
   * @see #getDecl
   */
  void setDecl(DeclName decl);
}
