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
import java.net.URL;
import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
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
  /**
   * A latex markup function cache.
   * It is basically a mapping from String, the name of a section,
   * to its LatexMarkupFunction.
   */
  private Map markupFunctions_ = new HashMap();

  /**
   * Returns the latex markup function for the given section name.
   */
  public LatexMarkupFunction getLatexMarkupFunction(String section)
  {
    LatexMarkupFunction result =
      (LatexMarkupFunction) markupFunctions_.get(section);
    if (result == null) {
      try {
        URL url = getClass().getResource("/lib/" + section + ".tex");
        LatexToUnicode l2u = new LatexToUnicode(url, this);
        while (l2u.next_token().sym != LatexSym.EOF) {
          // do nothing
        }
        Map markupFunctions = l2u.getMarkupFunctions();
        markupFunctions_.putAll(markupFunctions);
        result = (LatexMarkupFunction) markupFunctions_.get(section);
      }
      catch (Exception e) {
        String message = "Cannot get latex specification for " + section ;
        System.err.println(message);
        e.printStackTrace();
      }
    }
    return result;
  }

  public OperatorTable getOperatorTable(String section)
  {
    throw new UnsupportedOperationException();
  }

  public Term getAst(String section)
  {
    throw new UnsupportedOperationException();
  }
}
