/**
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.util;

import java.io.IOException;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Provides access to the logging API.
 */
public final class CztLogger
{
  /**
   * Do not create instances of this class.
   */
  private CztLogger()
  {
  }

  /**
   * Returns the appropriate logger for the given class.
   *
   * @param aClass the class that needs to log something.
   * @return a suitable Logger.
   */
  public static Logger getLogger(Class<?> aClass)
  {
    return Logger.getLogger(aClass.getName());
  }
  
  public final static boolean DEFAULT_SHOW_LOG_TIME_STAMP     = true;
  public final static boolean DEFAULT_SHOW_LOG_RECORD_MESSAGE = true;
  public final static boolean DEFAULT_SHOW_LOG_SOURCE_METHOD  = false;
  public final static boolean DEFAULT_SHOW_LOG_STACKTRACE     = true;
  public final static Level DEFAULT_HANDLER_LEVEL = Level.CONFIG;
      
  public static Formatter createLogFormatter()
  {
    return new SimpleFormatter(
      DEFAULT_SHOW_LOG_TIME_STAMP, 
      DEFAULT_SHOW_LOG_RECORD_MESSAGE, 
      DEFAULT_SHOW_LOG_SOURCE_METHOD,
      DEFAULT_SHOW_LOG_STACKTRACE);
  }
  
  public final static Formatter DEFAULT_LOG_FORMATTER = createLogFormatter();  
  
  public static Formatter createLogFormatter(boolean showTimeStamp, 
    boolean showRecordedMessage, boolean showSourceMethod, boolean showStackTrace)
  {
    return new SimpleFormatter(showTimeStamp, showRecordedMessage, 
      showSourceMethod, showStackTrace);
  }
  
  public static void setConsoleHandler(Logger logger)
  {
    setConsoleHandler(logger, DEFAULT_HANDLER_LEVEL);
  }
  
  public static void setConsoleHandler(Logger logger, Level handlerLevel)
  {
    setConsoleHandler(logger, handlerLevel, logger.getLevel());
  }
    
  public static void setConsoleHandler(Logger logger,
    Level handlerLevel, Level loggerLevel)
  {
    setConsoleHandler(logger, handlerLevel, loggerLevel, DEFAULT_LOG_FORMATTER);
  }

  public static void setConsoleHandler(Logger logger,
          Level handlerLevel, Level loggerLevel, Formatter formatter)
  {
    ConsoleHandler ch = getHandler(logger, ConsoleHandler.class);
    if (ch == null) 
    {
      ch = new ConsoleHandler();
      logger.addHandler(ch);
    }
    ch.setLevel(handlerLevel);
    ch.setFormatter(formatter);
    logger.setLevel(loggerLevel);
  }

  @SuppressWarnings("unchecked")
  public static <T extends Handler> T getHandler(Logger logger, Class<T> cls)
  {
    for(Handler h : logger.getHandlers())
    {
      if (cls.isInstance(h))
        return (T)h;
    }
    return null;
  }

  public static void removeHandlerClass(Logger logger, Class<?> cls)
  {
    for(Handler h : logger.getHandlers())
    {
      if (cls.isInstance(h))
        logger.removeHandler(h);
    }
  }
  
  public static void setFileHandler(Logger logger, String fileName)
  {
    setFileHandler(logger, DEFAULT_HANDLER_LEVEL, fileName);
  }    
  
  public static void setFileHandler(Logger logger, Level handlerLevel, String fileName)
  {
    setFileHandler(logger, handlerLevel, logger.getLevel(), fileName);
  }
  
  public static void setFileHandler(Logger logger, 
    Level handlerLevel, Level loggerLevel, String fileName)
  {        
    setFileHandler(logger, handlerLevel, loggerLevel, fileName, DEFAULT_LOG_FORMATTER);
  }

  public static void setFileHandler(Logger logger,
    Level handlerLevel, Level loggerLevel, String fileName, Formatter formatter)
  {
    logger.setLevel(loggerLevel);
    FileHandler fh = getHandler(logger, FileHandler.class);
    if (fh == null)
    {
      try
      {
        fh = new FileHandler(fileName);
      } catch (IOException e)
      {
        logger.config("Could not create file handler for logger " + logger.getName() +
          "\n\t An I/O exception was thrown while trying to create " + fileName +
          "\n\t I/O exception : " + e.getMessage());
        return ;
      }
      logger.addHandler(fh);
    }
    fh.setLevel(handlerLevel);
    fh.setFormatter(formatter);
  }
}

