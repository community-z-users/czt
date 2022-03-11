
/*
SimpleCircusFormatter.java
 *
Created on 05 February 2007, 15:23
 *
To change this template, choose Tools | Template Manager
and open the template in the editor.
 */
package net.sourceforge.czt.parser.circustime;

//~--- JDK imports ------------------------------------------------------------

import java.io.PrintWriter;
import java.io.StringWriter;

import java.text.MessageFormat;

import java.util.Date;
import java.util.logging.Formatter;
import java.util.logging.LogRecord;

//~--- classes ----------------------------------------------------------------

/**
 *
 * @author leo
 */
public class SimpleCircusTimeFormatter extends Formatter {
    private final static String format = "{0,date} {0,time}";

    //~--- fields -------------------------------------------------------------

    private Object     args[]               = new Object[1];
    private final Date dat                  = new Date();
    private boolean    fShowTimeStamp       = true;
    private boolean    fShowStackTrace      = true;
    private boolean    fShowSourceMethod    = true;
    private boolean    fShowRecordedMessage = true;
    @SuppressWarnings("unused")
	private boolean    fShowDirectory       = true;

    // Line separator string.  This is the value of the line.separator
    // property at the moment that the SimpleFormatter was created.
    // private String lineSeparator = (String) java.security.AccessController.doPrivileged(
    // new sun.security.action.GetPropertyAction("line.separator"));
    private String        lineSeparator = System.getProperty("line.separator");
    private MessageFormat formatter;

    //~--- constructors -------------------------------------------------------

    /**
     * Creates a new instance of SimpleCircusFormatter
     * @param showTimeStamp
     * @param showRecordedMessage
     * @param showSourceMethod
     * @param showDirectory
     * @param showStackTrace
     */
    public SimpleCircusTimeFormatter(boolean showTimeStamp,
                                 boolean showRecordedMessage,
                                 boolean showSourceMethod,
                                 boolean showDirectory,
                                 boolean showStackTrace) {
        fShowTimeStamp       = showTimeStamp;
        fShowRecordedMessage = showRecordedMessage;
        fShowSourceMethod    = showSourceMethod;
        fShowDirectory       = showDirectory;
        fShowStackTrace      = showStackTrace;
    }

    //~--- methods ------------------------------------------------------------

    /**
     * Format the given LogRecord.
     * @param record the log record to be formatted.
     * @return a formatted log record
     */
  @Override
    public synchronized String format(LogRecord record) {
        StringBuilder sb = new StringBuilder();

        if (fShowTimeStamp) {

            // Minimize memory allocations here.
            dat.setTime(record.getMillis());
            args[0] = dat;

            StringBuffer text = new StringBuffer();

            if (formatter == null) {
                formatter = new MessageFormat(format);
            }

            formatter.format(args, text, null);
            sb.append(text);
            sb.append(" ");
            sb.append(lineSeparator);
        }

        if (fShowSourceMethod) {
            if (record.getSourceClassName() != null) {
                sb.append(record.getSourceClassName());
            } else {
                sb.append(record.getLoggerName());
            }

            if (record.getSourceMethodName() != null) {
                sb.append(" ");
                sb.append(record.getSourceMethodName());
            }

            sb.append(lineSeparator);
        }

        if (fShowRecordedMessage) {
            String message = formatMessage(record);

            sb.append(record.getLevel().getLocalizedName());
            sb.append(": ");
            sb.append(message);
            sb.append(lineSeparator);
        }

        if (fShowStackTrace) {
            if (record.getThrown() != null) {
                try {
                    StringWriter sw = new StringWriter();
                    PrintWriter  pw = new PrintWriter(sw);

                    record.getThrown().printStackTrace(pw);
                    pw.close();
                    sb.append(sw.toString());
                } catch (Exception ex) {}
            }
        }

        return sb.toString();
    }
}