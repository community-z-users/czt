/*
  Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.session;

import java.util.List;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * <p>Provides a specific kind of information about sections.</p>
 *
 * <p>All classes that want to register to a SectionInfoRegistry
 * have to implement this interface.</p>
 *
 * @author Petra Malik
 */
public interface SectionInfoService
{
  /**
   * Returns the type of information provided.
   * A call to method {@link #run(ZSect)} should return an object of this type.
   */
  Class getInfoType();

  /**
   * Computes an object of type specified by the return value of
   * method {@link #getInfoType()} from the given Z section.
   */
  Object run(ZSect sect);

  /**
   * Computes an object of type specified by the return value of
   * method {@link #getInfoType()} from the given Z section.
   * The SectInfo object is used to lookup further information.
   */
  Object run(ZSect sect, SectionInfo sectInfo);
}
