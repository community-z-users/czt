/*
  Copyright (C) 2005, 2006 Petra Malik
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

package net.sourceforge.czt.parser.z;

import java.util.List;

import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.*;

/**
 * A Z parse error.
 *
 * @author Petra Malik
 */
public class ZParseError
  extends CztErrorImpl
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.parser.z.ZParseResourceBundle";

  public static void report(SectionInfo sectInfo,
                            Source source,
                            ErrorType errorType,
                            ZParseMessage msg,
                            Object[] params,
                            LocInfo locInfo)
  {
    report(sectInfo, source, errorType, msg, params, locInfo, null);
  }

  public static void report(SectionInfo sectInfo,
                            Source source,
                            ErrorType errorType,
                            ZParseMessage msg,
                            Object[] params,
                            LocInfo locInfo,
                            String info)
  {
    try {
      ParseException parseException = (ParseException)
        sectInfo.get(new Key(source.getName(),
                             ParseException.class));
      List<CztError> errorList = parseException.getErrors();
      ZParseError error = new ZParseError(msg, params, locInfo);
      error.setErrorType(errorType);
      error.setInfo(info);
      errorList.add(error);
    }
    catch (CommandException e) {
      e.printStackTrace();
    }
  }

  public ZParseError(ZParseMessage msg, Object[] params, LocInfo locInfo)
  {
    super(msg.toString(), params, locInfo);
  }

  protected String getResourceName()
  {
    return RESOURCE_NAME;
  }
}
