/*
 * SimpleCircusFormatter.java
 *
 * Created on 05 February 2007, 15:23
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circus;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.text.MessageFormat;
import java.util.Date;
import java.util.logging.Formatter;
import java.util.logging.LogRecord;

/**
 *
 * @author leo
 */
public class SimpleCircusFormatter extends Formatter
{
  
  private final static String format = "{0,date} {0,time}";
  
  private MessageFormat formatter;
  private Object args[] = new Object[1];
  private final Date dat = new Date();
  private boolean fShowTimeStamp = true;
  private boolean fShowRecordedMessage = true;
  private boolean fShowSourceMethod = true;
  private boolean fShowDirectory = true;
  private boolean fShowStackTrace = true;
  
  
  // Line separator string.  This is the value of the line.separator
  // property at the moment that the SimpleFormatter was created.
  //private String lineSeparator = (String) java.security.AccessController.doPrivileged(
  //        new sun.security.action.GetPropertyAction("line.separator"));
  private String lineSeparator = System.getProperty("line.separator");
  
  /** Creates a new instance of SimpleCircusFormatter */
  public SimpleCircusFormatter(boolean showTimeStamp, boolean showRecordedMessage,
      boolean showSourceMethod, boolean showDirectory, boolean showStackTrace)
  {
    fShowTimeStamp = showTimeStamp;
    fShowRecordedMessage = showRecordedMessage;
    fShowSourceMethod = showSourceMethod;
    fShowDirectory = showDirectory;
    fShowStackTrace = showStackTrace;
  }
  
  /**
   * Format the given LogRecord.
   * @param record the log record to be formatted.
   * @return a formatted log record
   */
  public synchronized String format(LogRecord record)
  {
    StringBuffer sb = new StringBuffer();
    if (fShowTimeStamp)
    {
      // Minimize memory allocations here.
      dat.setTime(record.getMillis());
      args[0] = dat;
      StringBuffer text = new StringBuffer();
      if (formatter == null)
      {
        formatter = new MessageFormat(format);
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
          StringWriter sw = new StringWriter();
          PrintWriter pw = new PrintWriter(sw);
          record.getThrown().printStackTrace(pw);
          pw.close();
          sb.append(sw.toString());
        }
        catch (Exception ex)
        {
        }
      }
    }
    return sb.toString();
  }
}
