/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.parser.util;

import java.util.Properties;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.SimpleFormatter;

/**
 *
 * @author Leo Freitas
 * @date Aug 4, 2011
 */
public abstract class TokeniserDebugger {

  // switch to have logging info? make this a property somewhere?
  private boolean debug_ = false;

  private static final SimpleFormatter formatter_ = new SimpleFormatter(false, true, false, false);

  protected TokeniserDebugger()
  {
    this(new Properties());
  }

  protected TokeniserDebugger(Properties properties)
  {
    // debug individual scanner/lexer/parser name (E.g., no need for package as we won't have two of them at once
    // or debug the whole lot if * is given. Defaults (e.g., if property is not present) are false.
    boolean d = Boolean.parseBoolean(properties.getProperty("czt.debug." + getClass().getSimpleName(), "false"))
             || Boolean.parseBoolean(properties.getProperty("czt.debug.*", "false"));
    setDebug(d);
  }

  protected Level getDebugLoggingLevel()
  {
    return Level.ALL;
  }

  protected final void setDebug(boolean v)
  {
    debug_ = v;
    if (!debug_)
      CztLogger.removeHandlerClass(CztLogger.getLogger(getClass()), ConsoleHandler.class);
    else
      CztLogger.setConsoleHandler(CztLogger.getLogger(getClass()), Level.ALL, getDebugLoggingLevel(), formatter_);
  }

  public boolean logDebugInfo()
  {
    return debug_;
  }

  public void logFormatted(String pattern, Object... args)
  {
    if (logDebugInfo())
    {
      final String logMessage = java.text.MessageFormat.format(pattern, args);
      doLog(logMessage);
    }
  }

  protected void doLog(final String alreadyFormattedMsg)
  {
    CztLogger.getLogger(getClass()).finer(alreadyFormattedMsg);
  }
}
