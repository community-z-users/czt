/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

import java.util.*;
import java.text.MessageFormat;
import java.io.StringWriter;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.SectionInfo;

/**
 * A class for annotating terms associated with error messages.
 */
public class ErrorAnn
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.typecheck.z.TypeCheckResources";
  private static ResourceBundle RESOURCE_BUNDLE =
    ResourceBundle.getBundle(RESOURCE_NAME);

  /** The error message. */
  protected ErrorMessage errorMessage_;

  /** The parameters associated with this error message. */
  protected Object [] params_;

  /** The section in which this error occurred. */
  protected String sectName_;

  /** The section info. */
  protected SectionInfo sectInfo_;

  /** The location information. */
  protected LocAnn locAnn_;

  public ErrorAnn(ErrorMessage errorMessage, Object [] params,
                  SectionInfo sectInfo, String sectName, LocAnn locAnn)
  {
    errorMessage_ = errorMessage;
    params_ = params;
    sectInfo_ = sectInfo;
    sectName_ = new String(sectName);
    locAnn_ = locAnn;
  }

  public void setErrorMessage(ErrorMessage errorMessage)
  {
    errorMessage_ = errorMessage;
  }

  public ErrorMessage getErrorMessage()
  {
    return errorMessage_;
  }

  public int getLine()
  {
    if (locAnn_ != null) {
      return locAnn_.getLine();
    }
    return -1;
  }

  public int getColumn()
  {
    if (locAnn_ != null) {
      return locAnn_.getCol();
    }
    return -1;
  }

  public String getSource()
  {
    if (locAnn_ != null) {
      return locAnn_.getLoc();
    }
    return null;
  }

  public String toString()
  {
    String result = new String();
    //format the error location as a string
    String localized = null;
    String [] args = null;
    if (locAnn_ != null) {
      final Integer lineNr = locAnn_.getLine();
      final String source = locAnn_.getLoc();
      localized =
        RESOURCE_BUNDLE.getString(ErrorMessage.ERROR_FILE_LINE.toString());
      args = new String [] {source, lineNr.toString()};
    }
    else {
      localized =
        RESOURCE_BUNDLE.getString(ErrorMessage.NO_LOCATION.toString());
      args = new String[] {};
    }
    MessageFormat form = new MessageFormat(localized);
    result += form.format(args) + ": ";

    //format the parameters and write into the message
    String formatted [] = new String[params_.length];
    for (int i = 0; i < params_.length; i++) {
      formatted[i] = format(params_[i], sectInfo_, sectName_);
    }
    localized = RESOURCE_BUNDLE.getString(errorMessage_.toString());
    form = new MessageFormat(localized);
    result += form.format(formatted);

    return result;
  }

  //converts a Term to a string
  protected String format(Object object, SectionInfo sectInfo, String sectName)
  {
    if (object instanceof Type) {
      return formatType((Type) object);
    }
    else if (object instanceof Term) {
      try {
        StringWriter writer = new StringWriter();
        PrintUtils.printUnicode((Term) object, writer, sectInfo, sectName);
        return writer.toString();
      }
      catch (Exception e) {
        String message = "Cannot be printed\n";
        return message;
      }
    }
    return object.toString();
  }

  protected String formatType(Type type)
  {
    //TypeFormatter formatter = new TypeFormatter();
    //Expr expr = (Expr) type.accept(formatter);
    //return format(expr);
    return type.toString();
  }
}

