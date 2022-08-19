/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.parser.z;

import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

public enum ZOpToken
  implements Token
{
  I(NewlineCategory.BOTH),
  IP(NewlineCategory.BOTH),
  EL(NewlineCategory.BOTH),
  ELP(NewlineCategory.BOTH),
  ERE(NewlineCategory.BOTH),
  EREP(NewlineCategory.BOTH),
  ES(NewlineCategory.BOTH),
  SS(NewlineCategory.BOTH),
  SRE(NewlineCategory.BOTH),
  SREP(NewlineCategory.BOTH),

  PRE(NewlineCategory.AFTER),
  PREP(NewlineCategory.AFTER),
  L(NewlineCategory.AFTER),
  LP(NewlineCategory.AFTER),

  POST(NewlineCategory.BEFORE),
  POSTP(NewlineCategory.BEFORE),
  ER(NewlineCategory.BEFORE),
  ERP(NewlineCategory.BEFORE),
  SR(NewlineCategory.BEFORE),
  SRP(NewlineCategory.BEFORE);

  private NewlineCategory newlineCategory_;

  ZOpToken(NewlineCategory newlineCategory)
  {
    newlineCategory_ = newlineCategory;
  }

  public String getName()
  {
    return toString();
  }

  public Object getSpelling()
  {
    return null;
  }

  public String spelling()
  {
    return null;
  }

  public NewlineCategory getNewlineCategory()
  {
    return newlineCategory_;
  }
}
