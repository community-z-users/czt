/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval;

import java.util.logging.*;

/** This is a Logger formatter that prints readable indented messages.
 *  It is for formatting log messages in java.util.logging package.
 *  It records the ENTRY/EXIT log records to indent messages so
 *  that they reflect the call stack.  It ignores (does not display)
 *  a lot of information like full package names, levels, times, threads.
 *  To install this formatter, do something like this:
 *  <pre>
    // set the logger to use a human-readable format
    Handler fh = new FileHandler("zlive.log");
    fh.setFormatter(new ZFormatter());
    Logger.getLogger(...).addHandler(fh);
    </pre>
 */
public class ZFormatter extends SimpleFormatter {
  private int depth = 0;

  private final String PARAM_PREFIX = "\t\t";

  private static Handler handler_;

  /** Helper method to start recording log messages to the
   *  given file using the ZFormatter class as the formatter.
   *  @param fileName  the name of the log file
   *  @param detail    Eg. Level.FINEST.
   */
  public static void startLogging(String where, String fileName, Level detail)
  {
    // set up a specific logger with our human-readable format
    Logger logger = Logger.getLogger(where);
    logger.setLevel(detail);
    if (handler_ == null) {
      try {
        handler_ = new FileHandler(fileName);
        handler_.setLevel(detail);
        handler_.setEncoding("utf8");
        handler_.setFormatter(new ZFormatter());
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    }
    logger.addHandler(handler_);
    logger.setUseParentHandlers(false); // just use this handler
  }

  /** Stop the log messages that were started by startLogging. */
  public static void stopLogging(String where)
  {
    Logger logger = Logger.getLogger(where);
    logger.removeHandler(handler_);
    handler_ = null;
  }

  public String format(LogRecord record)
  {
    String cls = record.getSourceClassName();
    cls = cls.substring(cls.lastIndexOf('.')+1); // strip package name
    String meth = record.getSourceMethodName();
    String msg = record.getMessage();

    // indent
    if (msg.startsWith("ENTRY"))
      depth++;
    StringBuffer indent = new StringBuffer();
    indent.append(depth);
    for (int i=0; i<depth; i++)
      indent.append("  ");

    // process parameters
    StringBuffer params = new StringBuffer();
    Object args[] = record.getParameters();
    if (args != null) {
      for (int i=0; i<args.length; i++) {
        Object arg = args[i];
        String argstr = (arg==null) ? "null" : arg.toString();
        params.append(PARAM_PREFIX + i + "=" + argstr + "\n");
      }
    }

    if (msg.startsWith("RETURN"))
      depth--;
    else if (msg.startsWith("THROW")) {
      depth--;
      Throwable ex = record.getThrown();
      if (ex != null)
        params.append(PARAM_PREFIX + ex.toString() + "\n");
    }
    //assert depth >= 0;

    return indent + cls + ":" + meth
      + " " + msg + "\n" + params;
  }
}