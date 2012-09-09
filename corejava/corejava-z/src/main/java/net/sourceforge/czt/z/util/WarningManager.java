/*
Copyright (C) 2006 Leo Freitas
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
package net.sourceforge.czt.z.util;

import net.sourceforge.czt.util.Section;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.util.CztLogger;

/**
 *
 * @author Leo Freitas
 */
public class WarningManager
{

  private String currentSectName_;
  private Class<?> loggerClass_;
  private final TreeMap<String, List<String>> sectWarnings_;

  public enum WarningOutput { SHOW, HIDE, RAISE };
  
  private WarningOutput warningOutput_;

  public WarningManager()
  {
    loggerClass_ = getClass();
    currentSectName_ = Section.ANONYMOUS.getName();
    warningOutput_ = WarningOutput.SHOW;
    sectWarnings_ = new TreeMap<String, List<String>>();
  }

  /** Creates a new instance of WarningManager
   * @param forLogger 
   */
  public WarningManager(Class<?> forLogger)
  {
    this();
    setLoggerClass(forLogger);   
  }

  /**
   * Derived classes can change the formatting to take into account, say,
   * pretty printing.
   * @param message
   * @param arguments
   * @return
   */
  protected String format(String message, Object... arguments)
  {
    return MessageFormat.format(message, arguments);
  }

  public Map<String, List<String>> getZSectWarnings()
  {
    return Collections.unmodifiableSortedMap(sectWarnings_);
  }

  public void clear()
  {
    sectWarnings_.clear();
  }

  public String getCurrentSectName()
  {
    String result = currentSectName_;
    if (result == null || result.isEmpty())
    {
      result = Section.ANONYMOUS.getName();
    }
    return result;
  }

  public void setCurrentSectName(String sectName)
  {
    currentSectName_ = sectName;
  }

  public Class<?> getLoggerClass()
  {
    return loggerClass_;
  }

  public final Class<?> setLoggerClass(Class<?> cls)
  {
    Class<?> old = loggerClass_;
    loggerClass_ = cls;
    return old;
  }

  protected String createWarning(String message, Object... arguments)
  {
    final String msg = format(message, arguments);
    final String sect = getCurrentSectName();
    if (!sectWarnings_.containsKey(sect))
    {
      sectWarnings_.put(sect, new ArrayList<String>(PerformanceSettings.INITIAL_ARRAY_CAPACITY));
    }
    sectWarnings_.get(sect).add(msg);
    return msg;
  }

  protected void doWarn(String msg)
  {
    // only output when showing. Raise adds it to errors elsewhere, and hides does nothing
    if (warningOutput_.equals(WarningOutput.SHOW))
    {
      CztLogger.getLogger(loggerClass_).warning(msg);
    }
  }

  /**
   * Basic warning method it creates a warning message by formatting
   * the given message with the given arguments, and adding such 
   * warning to the map of warnings under the current section name as key.
   * Finally, it warns the message using the current logger class.
   * @param message warning string to be formatted
   * @param arguments formatting arguments
   */
  public void warn(String message, Object... arguments)
  {
    String str = createWarning(message, arguments);
    doWarn(str);
  }

  public void setWarningOutput(WarningOutput out)
  {
    assert out != null;
    warningOutput_ = out;
  }

  public WarningOutput getWarningOutput()
  {
    return warningOutput_;
  }
}
