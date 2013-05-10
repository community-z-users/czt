/*
  Copyright (C) 2004, 2006 Petra Malik
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

import java.util.ArrayList;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.session.*;

public class ParseExceptionCommand
  implements Command
{
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    final Key<ParseException> key = new Key<ParseException>(name, ParseException.class);
    if (! manager.isCached(key)) {
      // parser exception has no dependencies
      manager.endTransaction(key, new ParseException(manager.getDialect(), 
    		  new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY)));
    }
    return true;
  }
}
