/*
  Copyright (C) 2004, 2006, 2007 Petra Malik
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

import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.session.CommandException;

/**
 * A parse exception.  It contains a list of errors that caused the
 * parse to fail.
 *
 * @author Petra Malik
 */
public class ParseException
  extends CommandException
  implements CztErrorList
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 2265450712247923060L;
private final List<CztError> errorList_;

  public ParseException()
  {
    errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }
  /**
   * Constructs a new parse exception with the specified error list.
   * @param errorList
   */
  public ParseException(List<CztError> errorList)
  {
    this();
    errorList_.addAll(errorList);
  }

  public ParseException(CztError error)
  {
    this();
    errorList_.add(error);
  }

  public List<CztError> getErrorList()
  {
    return errorList_;
  }

  @Override
  public List<CztError> getErrors()
  {
    return errorList_;
  }

  public void printErrorList()
  {
    for (CztError parseError : errorList_) {
      System.err.println(parseError.toString());
    }
  }

  @Override
  public String getMessage()
  {
    StringBuilder result = new StringBuilder();
    for (CztError parseError : errorList_) {
      result.append("\n").append(parseError.toString());
    }
    return result.toString();
  }
}
