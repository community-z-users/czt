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

package net.sourceforge.czt.print.z;

import java.util.List;
import java.util.ResourceBundle;

import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.session.*;

/**
 * A Z print error.
 *
 * @author Leo Freitas
 */
public class ZPrintError
  extends CztErrorImpl
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.print.z.ZPrintResourceBundle";

  public static void report(SectionInfo sectInfo,
                            Source source,
                            ErrorType errorType,
                            ZPrintMessage msg,
                            Object[] params,
                            LocInfo locInfo)
  {
    report(sectInfo, source, errorType, msg, params, locInfo, null);
  }

  public static void report(SectionInfo sectInfo,
                            Source source,
                            ErrorType errorType,
                            ZPrintMessage msg,
                            Object[] params,
                            LocInfo locInfo,
                            String info)
  {
    ZPrintError error = new ZPrintError(sectInfo, msg, params, locInfo);
    error.setErrorType(errorType);
    error.setInfo(info);
    report(source, error);
  }
  
  public static void report(Source source, CztError error)
  {
	if (error.hasSectionInfo())
	{
    try {
      PrintException printException = error.getSectionInfo().get(
          new Key<PrintException>(source.getName(), PrintException.class));
      List<CztError> errorList = printException.getErrors();
      errorList.add(error);
    }
    catch (CommandException e) {
      e.printStackTrace();
    }
	}
  }

  public ZPrintError(SectionInfo si, ZPrintMessage msg, Object[] params, LocInfo locInfo)
  {
    super(si, msg.toString(), params, locInfo);
  }

  @Override
  protected ResourceBundle getResourceBundle()
  {
    return ResourceBundle.getBundle(RESOURCE_NAME);
  }
}
