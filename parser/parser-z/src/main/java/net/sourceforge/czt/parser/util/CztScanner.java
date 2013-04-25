/**
Copyright (C) 2004 Petra Malik
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

//import java.io.FileNotFoundException;

import net.sourceforge.czt.session.Dialect;
import java_cup.runtime.Scanner;
import java_cup.runtime.Symbol;

public interface CztScanner
  extends Scanner
{
  //void reset(String filename) throws FileNotFoundException; NEVER USED; REMOVED
  boolean logDebugInfo();
  void logSymbol(Symbol symbol);
  void logFormatted(String pattern, Object... args);
  
  Dialect getDialect();
}
