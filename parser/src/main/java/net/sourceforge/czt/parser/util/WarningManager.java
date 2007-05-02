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
package net.sourceforge.czt.parser.util;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.util.Section;

/**
 *
 * @author Leo Freitas
 */
public class WarningManager {
    
    private String currentSectName_;
    private final Class<?> loggerClass_;
    private final TreeMap<String, List<String>> sectWarnings_;
    
    public WarningManager() {
        loggerClass_ = getClass();
        currentSectName_ = Section.ANONYMOUS.getName();
        sectWarnings_ = new TreeMap<String, List<String>>();
    }
    
    /** Creates a new instance of WarningManager */
    public WarningManager(Class<?> forLogger) {        
        loggerClass_ = forLogger;
        currentSectName_ = Section.ANONYMOUS.getName();
        sectWarnings_ = new TreeMap<String, List<String>>();
    }
    
    public Map<String, List<String>> getZSectWarnings() {
        return Collections.unmodifiableSortedMap(sectWarnings_);
    }
    
    public void clear() {
        sectWarnings_.clear();
    }
    
    public String getCurrentSectName() {
        String result = currentSectName_;
        if (result == null || result.isEmpty())
            result = Section.ANONYMOUS.getName();
        return result;
    }
    
    public void setCurrentSectName(String sectName) {
        currentSectName_ = sectName;
    }
    
    public Class<?> getLoggerClass() {
        return loggerClass_;
    }
    
    public void warn(String message, Object... arguments) {
      final String msg = MessageFormat.format(message, arguments);      
      final String sect = getCurrentSectName();
      if (!sectWarnings_.containsKey(sect)) {          
          sectWarnings_.put(sect, new ArrayList<String>());        
      }
      sectWarnings_.get(sect).add(msg);
      CztLogger.getLogger(loggerClass_).warning(msg);
  }     
}
