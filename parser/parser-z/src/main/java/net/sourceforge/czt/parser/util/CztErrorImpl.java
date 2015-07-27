/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

import java.text.MessageFormat;
import java.util.ResourceBundle;

import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztLogger;

/**
 * An abstract CztError that can be localised.
 *
 * @author Petra Malik
 */
public abstract class CztErrorImpl
  extends LocInfoImpl
  implements CztError
{
  private final String message_;
  private final Object[] params_;
  private final SectionInfo sectInfo_;

  private String info_ = null;
  private ErrorType errorType_ = ErrorType.ERROR;

  public CztErrorImpl(SectionInfo si, String message, Object[] params, LocInfo locInfo)
  {
    super(locInfo);
    sectInfo_ = si;
    message_ = message;
    params_ = params.clone();
  }

  protected abstract ResourceBundle getResourceBundle();
  
  @Override
  public boolean hasSectionInfo()
  {
	  if (sectInfo_ == null)
	  {
		  CztLogger.getLogger(getClass()).severe(getClass().getName() + " has no SectionInfo set, but it is being accessed.");
	  }
	  return sectInfo_ != null;
  }
  
  @Override
  public SectionInfo getSectionInfo()
  {
	  return sectInfo_;
  }

  public String getMessage()
  {
    String localized = getResourceBundle().getString(message_);
    MessageFormat form = new MessageFormat(localized);
    return form.format(params_);
  }

  public void setErrorType(ErrorType errorType)
  {
    errorType_ = errorType;
  }

  public ErrorType getErrorType()
  {
    return errorType_;
  }

  public String getInfo()
  {
    return info_;
  }

  public void setInfo(String info)
  {
    info_ = info;
  }

  public String toString()
  {
    return super.toString() + ": " + getMessage();
  }

  protected String getMessageKey()
  {
    return message_;
  }

  protected Object[] getMessageParams()
  {
    return params_;
  }

  public int compareTo(CztError other)
  {
    return compareCztErrorPositionTypeAndMessage(this, other);
  }
  
  public boolean equals(Object obj)
  {
	  if (obj != null &&
		        this.getClass().equals(obj.getClass())) {
		  CztErrorImpl cei = (CztErrorImpl)obj;
		  return compareTo(cei) == 0;
	  }
	  return false;
  }
  
  public int hashCode()
  {
	  int h = super.hashCode();
	  h += baseHashCodeCztError(this);
	  return h;
  }
  
  public static boolean compareCztErrorsEquals(CztError error1, Object error2)
  {
	 boolean result = error1 == null && error2 == null;
	 if (!result)
	 {
		 if (error1 != null)
		 {
			 result = error1.equals(error2);
		 }
		 //result = error1 != null ? error1.equals(error2) : error2.equals(error1);
	 }
	 return result; 
  }
  
  public static int baseHashCodeCztError(CztError error)
  {
	  if (error == null) throw new NullPointerException();
	  int h = error.getLine();
	  h += error.getColumn();
	  h += error.getErrorType().hashCode();
	  h += error.getMessage().hashCode();
	  return h;
  }

  public static int compareCztErrorPositionTypeAndMessage(CztError error1, CztError error2)
  {
	if (error1 == null || error2 == null)
		throw new NullPointerException("Cannot compare null CztErrors");
    int result = 0;
    result = error1.getLine() - error2.getLine();
    if (result == 0) {
      result = error1.getColumn() - error2.getColumn();
    }
    if (result == 0) {
      result = error1.getErrorType().compareTo(error2.getErrorType());
    }
    if (result == 0) {
      result = error1.getMessage().compareTo(error2.getMessage());
    }
    return result;
  }
}
