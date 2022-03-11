/*
  Copyright (C) 2006 Petra Malik
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation); either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY); without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt); if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.oz;

import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

public enum OzToken
  implements Token
{
  CLASS(ZString.SCH + ZString.SPACE + "class", NewlineCategory.BOTH),
  GENCLASS(ZString.SCH + ZString.SPACE + "genclass", NewlineCategory.BOTH),
  STATE(ZString.SCH + ZString.ZEDCHAR, NewlineCategory.BOTH),
  INIT(ZString.SCH + ZString.SPACE + OzString.INITWORD, NewlineCategory.BOTH),
  OPSCH(ZString.SCH +  "op", NewlineCategory.BOTH),
  SDEF(ZString.SPACE + OzString.SDEF, NewlineCategory.BOTH),
  OPNAME(NewlineCategory.AFTER),
  DEFNAME(NewlineCategory.NEITHER),
  SCOPE(NewlineCategory.BOTH);  

  private String spelling_ = null;
  private NewlineCategory newlineCategory_;

  OzToken(NewlineCategory newlineCategory)
  {
    newlineCategory_ = newlineCategory;
  }

  OzToken(String spelling, NewlineCategory newlineCategory)
  {
    spelling_ = spelling;
    newlineCategory_ = newlineCategory;
  }

  public String getName()
  {
    return toString();
  }

  public Object getSpelling()
  {
    return spelling_;
  }

  public String spelling()
  {
    return spelling_;
  }

  public NewlineCategory getNewlineCategory()
  {
    return newlineCategory_;
  }
}
