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

import java.util.logging.Logger;

/**
 * An abstract debug class that provides methods for logging.
 *
 * @author Petra Malik
 */
public abstract class Debug
{
  /**
   * Returns the class name of this class.
   */
  protected String getClassName()
  {
    return getClass().getName();
  }

  /**
   * Returns the logger that is used
   * when logging messages are written.
   */
  protected Logger getLogger()
  {
    return Logger.getLogger(getClassName());
  }

  protected void logFine(String message)
  {
    getLogger().fine(message);
  }

  protected void logInfo(String message)
  {
    getLogger().info(message);
  }

  protected void logSevere(String message)
  {
    getLogger().severe(message);
  }

  protected void logEntering(String methodName)
  {
    getLogger().entering(getClassName(), methodName);
  }

  protected void logEntering(String methodName, Object argument)
  {
    getLogger().entering(getClassName(), methodName, argument);
  }

  protected void logExiting(String methodName)
  {
    getLogger().exiting(getClassName(), methodName);
  }

  protected void logExiting(String methodName, Object returnValue)
  {
    getLogger().exiting(getClassName(), methodName, returnValue);
  }
}
