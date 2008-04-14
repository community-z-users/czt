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
import java.io.*;
import java.text.MessageFormat;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;

/**
 * A class for annotating terms associated with error messages.
 */
public class ErrorAnn
  extends CztErrorImpl
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.typecheck.z.TypeCheckResources";
  private static ResourceBundle RESOURCE_BUNDLE =
    ResourceBundle.getBundle(RESOURCE_NAME);

  /** The section in which this error occurred. */
  protected String sectName_;

  /** The section info. */
  protected SectionManager manager_;

  /** The location information. */
  protected LocAnn locAnn_;

  /** The term that is in error. */
  protected Term term_;

  /** The markup to be printed. */
  protected Markup markup_;

  public ErrorAnn(String errorMessage, Object [] params,
                  SectionManager manager, String sectName,
                  LocAnn locAnn, Markup markup)
  {
    this(errorMessage, params, manager, sectName, locAnn, null, markup);
  }

  public ErrorAnn(String errorMessage, Object [] params,
                  SectionManager manager, String sectName,
                  LocAnn locAnn, Term term, Markup markup)
  {
    super(errorMessage, params, null);
    manager_ = manager;
    sectName_ = new String(sectName);
    locAnn_ = locAnn;
    term_ = term;
    markup_ = markup;
  }

  protected String getResourceName()
  {
    return RESOURCE_NAME;
  }

  public String getErrorMessage()
  {
    return getMessageKey();
  }

  public int getLine()
  {
    if (locAnn_ != null && locAnn_.getLine() != null) {
      return locAnn_.getLine().intValue();
    }
    return -1;
  }

  public int getColumn()
  {
    if (locAnn_ != null && locAnn_.getCol() != null) {
      return locAnn_.getCol().intValue();
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

  public void setTerm(Term term)
  {
    term_ = term;
  }

  public int getStart()
  {
    if (locAnn_ != null && locAnn_.getStart() != null) {
      return locAnn_.getStart().intValue();
    }
    return -1;
  }

  public int getLength()
  {
    if (locAnn_ != null && locAnn_.getLength() != null) {
      return locAnn_.getLength().intValue();
    }
    return -1;
  }

  public Term getTerm()
  {
    return term_;
  }

  public void setMarkup(Markup markup)
  {
    markup_ = markup;
  }

  public Markup getMarkup()
  {
    return markup_;
  }

  public String getMessage()
  {
    Object[] params = getMessageParams();
    //format the parameters and write into the message
    String formatted [] = new String[params.length];
    for (int i = 0; i < params.length; i++) {
      formatted[i] = format(params[i], manager_, sectName_);
    }
    String localised = RESOURCE_BUNDLE.getString(getMessageKey());
    MessageFormat form = new MessageFormat(localised);
    return form.format(formatted);
  }
  
  public static String getStringFromResourceBundle(String key)
  {
    return RESOURCE_BUNDLE.getString(key);
  }

  public String toString()
  {
    String result = new String();
    //format the error location as a string
    String localised = null;
    String [] args = null;
    if (locAnn_ != null) {
      final String lineNr = locAnn_.getLine() != null ?
        locAnn_.getLine().toString() : "unknown";
      final String source = locAnn_.getLoc();
      localised =
        RESOURCE_BUNDLE.getString(ErrorMessage.ERROR_FILE_LINE.toString());
      args = new String [] {source, lineNr };
    }
    else {
      localised =
        RESOURCE_BUNDLE.getString(ErrorMessage.NO_LOCATION.toString());
      args = new String[] {};
    }

    MessageFormat form = new MessageFormat(localised);
    result += form.format(args) + ": ";

    result += getMessage();

    return result;
  }

  //converts a Term to a string
  protected String format(Object object,
                          SectionManager manager,
                          String sectName)
  {
    if (object instanceof Term) {
      try {
        Term term = (Term) ((Term) object).accept(getCarrierSet());
        StringWriter writer = new StringWriter();
        print(term, writer, manager, sectName, markup_);
        return writer.toString();
      }
      catch (Exception e) {
        String message = "Cannot be printed";
        e.printStackTrace();
        if (object instanceof Type) {
          message = object.toString();
        }
        return message;
      }
    }
    else if (object != null) {
      return object.toString();
    }
    return "Cannot be printed";
  }

  protected CarrierSet getCarrierSet()
  {
    return new CarrierSet(true);
  }

  protected void print(Term term,
                       Writer writer,
                       SectionManager manager,
                       String sectName,
                       Markup markup)
  {
    PrintUtils.print(term, writer, manager, sectName, markup);
  }
}
