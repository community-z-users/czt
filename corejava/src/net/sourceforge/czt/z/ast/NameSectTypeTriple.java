
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstInterface.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.z.ast;

import net.sourceforge.czt.base.ast.*;

/**
 * 
        A tuple consisting of a name, a section, and a type.
      
 *
 * @author Gnast version 0.1
 */
public interface NameSectTypeTriple extends Term
{

  /**
   * Returns the Name element.
   *
   * @return the Name element.
   */
  DeclName getName();

  /**
   * Sets the Name element.
   *
   * @param name   the Name element.
   * @see #getName
   */
  void setName(DeclName name);

  /**
   * Returns the Sect element.
   *
   * @return the Sect element.
   */
  String getSect();

  /**
   * Sets the Sect element.
   *
   * @param sect   the Sect element.
   * @see #getSect
   */
  void setSect(String sect);

  /**
   * Returns the Type element.
   *
   * @return the Type element.
   */
  Type getType();

  /**
   * Sets the Type element.
   *
   * @param type   the Type element.
   * @see #getType
   */
  void setType(Type type);
}
