/*
  Copyright (C) 2005 Petra Malik
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

import java.util.ListResourceBundle;

public class ParseResources
  extends ListResourceBundle
  implements ParseResourcesKeys
{
  private static final Object[][] contents_ = {
    { MSG_UNKNOWN_LATEX_COMMAND,
      "Unknown latex command {0} {1}" },
    { MSG_UNMATCHED_BRACES,
      "Unmatched braces {0} {1}" },
    { MSG_UNEXPECTED_TOKEN,
      "Unexpected token {0} {1}" },
  };

  public Object[][] getContents()
  {
    return contents_;
  }
}
        
