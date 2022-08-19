/*
 * Copyright (C) 2008 Leo Freitas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */package net.sourceforge.czt.util;

import java.util.Date;
import java.util.logging.Formatter;

/**
 * A simple log formatter that can be used for file handle formats.
 * @author leo
 */
public class SimpleFormatter extends Formatter
{

  private Date dat = new Date();
  private final static String format = "{0,date} {0,time}";
  private java.text.MessageFormat formatter;
  private Object args[] = new Object[1];
  private boolean fShowTimeStamp = true;
  private boolean fShowRecordedMessage = true;
  private boolean fShowSourceMethod = true;
  private boolean fShowStackTrace = true;
  // Line separator string.  This is the value of the line.separator
  // property at the moment that the SimpleFormatter was created.
  //private String lineSeparator = (String) java.security.AccessController.doPrivileged(
  //        new sun.security.action.GetPropertyAction("line.separator"));
  private String lineSeparator = "\r\n";//System.getProperty("line.separator");
  public SimpleFormatter(boolean showTimeStamp, boolean showRecordedMessage,
    boolean showSourceMethod, boolean showStackTrace)
  {
    fShowTimeStamp = showTimeStamp;
    fShowRecordedMessage = showRecordedMessage;
    fShowSourceMethod = showSourceMethod;
    fShowStackTrace = showStackTrace;
  }

  /**
   * Format the given LogRecord.
   * @param record the log record to be formatted.
   * @return a formatted log record
   */
  @Override
  public synchronized String format(java.util.logging.LogRecord record)
  {
    StringBuilder sb = new StringBuilder();
    if (fShowTimeStamp)
    {
      // Minimize memory allocations here.
      dat.setTime(record.getMillis());
      args[0] = dat;
      StringBuffer text = new StringBuffer();
      if (formatter == null)
      {
        formatter = new java.text.MessageFormat(format);
      }
      formatter.format(args, text, null);
      sb.append(text);
      sb.append(" ");
      sb.append(lineSeparator);
    }
    if (fShowSourceMethod)
    {
      if (record.getSourceClassName() != null)
      {
        sb.append(record.getSourceClassName());
      }
      else
      {
        sb.append(record.getLoggerName());
      }
      if (record.getSourceMethodName() != null)
      {
        sb.append(" ");
        sb.append(record.getSourceMethodName());
      }
      sb.append(lineSeparator);
    }
    if (fShowRecordedMessage)
    {
      String message = formatMessage(record);
      sb.append(record.getLevel().getLocalizedName());
      sb.append(": ");
      sb.append(message);
      sb.append(lineSeparator);
    }
    if (fShowStackTrace)
    {
      if (record.getThrown() != null)
      {
        try
        {
          java.io.StringWriter sw = new java.io.StringWriter();
          java.io.PrintWriter pw = new java.io.PrintWriter(sw);
          record.getThrown().printStackTrace(pw);
          pw.close();
          sb.append(sw.toString());
        }
        catch (Exception ex)
        {
          sb.append("Exception thrown: ");
          sb.append(ex.toString());
        }
      }
    }
    return sb.toString();
  }
}
