/*
 * CommunityZToolsPlugin.java
 * Copyright (C) 2004, 2005 Petra Malik
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
 */

import java.util.Vector;
import java.util.logging.*;
import java.util.prefs.*;

import net.sourceforge.czt.parser.util.ParseResources;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.z.Latex2Unicode;

import org.gjt.sp.jedit.*;
import errorlist.*;


public class CommunityZToolsPlugin extends EditPlugin
{
  protected static final DefaultErrorSource errorSource_ =
    new DefaultErrorSource("CZT");
  private static final Handler handler_ = new ErrorHandler();
  public static final String OPTION_PREFIX = "options.czt.";
  public static final String PROP_SPACE_BEFORE_PUNCTATION =
    "CommunityZToolsPlugin.addSpaceBeforeLatexPunctation";
  private static final String LOGGER_NAME = "net.sourceforge.czt";

  public void start()
  {
    ErrorSource.registerErrorSource(errorSource_);
    Logger.getLogger(LOGGER_NAME).addHandler(handler_);
  }

  public void stop()
  {
    Logger.getLogger(LOGGER_NAME).removeHandler(handler_);
    ErrorSource.unregisterErrorSource(errorSource_);
  }

  private static class ErrorHandler
    extends StreamHandler
  {
    public void publish(LogRecord record)
    {
      final Level level = record.getLevel();
      if (level == Level.WARNING || level == Level.SEVERE) {
        LocInfo locInfo = null;
        final Object[] params = record.getParameters();
        if (params.length > 0) {
          Object last = params[params.length - 1];
          if (last instanceof LocInfo) {
            locInfo = (LocInfo) last;
          }
        }
        final int errorType = level == Level.SEVERE ?
          ErrorSource.ERROR : ErrorSource.WARNING;
        final String source = locInfo != null && locInfo.getSource() != null ?
          locInfo.getSource() : "?";
        final int line = locInfo != null && locInfo.getLine() >= 0 ?
          locInfo.getLine() : 0;
        final int column = locInfo != null && locInfo.getColumn() >= 0 ?
          locInfo.getColumn() : 0;
        final int length = 0;
        final Formatter formatter = getFormatter();
        String message = formatter != null ?
          formatter.formatMessage(record) : record.getMessage();
        if (locInfo != null &&
            message.endsWith(locInfo.toString())) {
          final int endIndex = message.length() - locInfo.toString().length();
          message = message.substring(0, endIndex);
        }
        DefaultErrorSource.DefaultError error = 
          new DefaultErrorSource.DefaultError(errorSource_,
                                              errorType,
                                              source,
                                              line,
                                              column,
                                              length,
                                              message);
        errorSource_.addError(error);
      }
    }
  }
}
