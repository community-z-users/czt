/**
Copyright 2003 Petra Malik
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

package net.sourceforge.czt.gnast;

import java.util.Properties;

/**
 * Project properties.
 *
 * @author Petra Malik
 */
public interface ProjectProperties
{
  /**
   * Returns the name of this project.
   *
   * @return the name of this project.  Should never be <code>null</code>.
   */
  public String getName();

  /**
   * Returns the name of the package where all the AST interfaces go in.
   *
   * @return the AST interface package name.
   */
  public String getAstPackage();

  /**
   * Returns the name of the package where all the AST
   * implementation classes go in.
   *
   * @return the AST (implementation) class package name.
   */
  public String getImplPackage();
}
