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

package net.sourceforge.czt.session;

import java.io.*;
import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.LatexSym;
import net.sourceforge.czt.parser.util.Settings;
import net.sourceforge.czt.parser.z.LatexToUnicode;
import net.sourceforge.czt.parser.z.OperatorTable;

/**
 * This class provides some services like computing
 * the markup function for a given section name.
 */
public class SectionManager
{
  Map markupFunctions_ = new HashMap();

  public Map getLatexMarkupFunction(String sectionname)
  {
    Map result = (Map) markupFunctions_.get(sectionname);
    if (result == null) {
      try {
        String filename = Settings.getCztLib() + "/" + sectionname + ".tex";
        LatexToUnicode l2u = new LatexToUnicode(filename, this);
        while ( l2u.next_token().sym != LatexSym.EOF) {
          // do nothing
        }
        result = l2u.getMarkupFunction();
        markupFunctions_.put(sectionname, result);
      }
      catch (Exception e) {
        String message = "Cannot get latex specification for " + sectionname ;
        System.err.println(message);
        e.printStackTrace();
      }
    }
    return result;
  }

  public OperatorTable getOperatorTable(String sectionname)
  {
    throw new UnsupportedOperationException();
  }

  public Term getAst(String sectionname)
  {
    throw new UnsupportedOperationException();
  }
}
