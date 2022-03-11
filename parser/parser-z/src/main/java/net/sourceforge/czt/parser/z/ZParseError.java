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
import java.util.ResourceBundle;

import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.Source;

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
    ZParseError error = new ZParseError(sectInfo, msg, params, locInfo);
    error.setErrorType(errorType);
    error.setInfo(info);
    report(source, error);
  }
  
  public static void report(Source source, CztError error)
  {
	if (error.hasSectionInfo())
	{
	    try {
	      ParseException parseException = error.getSectionInfo().get(
	          new Key<ParseException>(source.getName(), ParseException.class));
	      List<CztError> errorList = parseException.getErrors();
	      errorList.add(error);
	    }
	    catch (CommandException e) {
	      e.printStackTrace();
	    }
	}
  }

  public ZParseError(SectionInfo si, ZParseMessage msg, Object[] params, LocInfo locInfo)
  {
    super(si, msg.toString(), params, locInfo);
  }

  @Override
  protected ResourceBundle getResourceBundle()
  {
    return ResourceBundle.getBundle(RESOURCE_NAME);
  }
}
