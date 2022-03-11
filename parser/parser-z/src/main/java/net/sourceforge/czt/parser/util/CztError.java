/*
  Copyright 2006 Petra Malik
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

package net.sourceforge.czt.parser.util;

import net.sourceforge.czt.session.SectionInfo;

/**
 * An error that contains enough information to be helpful to a user,
 * that is, somebody who processes Z specification using CZT tools.
 * Such an error should contain source, line, and column number
 * information.  Typical examples of such errors are scan, parse, and
 * typecheck errors.
 *
 * @author Petra Malik
 */
public interface CztError
  extends LocInfo, Comparable<CztError>
{
  String getMessage();
  ErrorType getErrorType();

  /**
   * Returns a more detailed description of this error and/or possible
   * fixes.  Might be <code>null</code> if no additional information
   * is available for this error.
   */
  String getInfo();
  
  boolean hasSectionInfo();
  SectionInfo getSectionInfo();
}
