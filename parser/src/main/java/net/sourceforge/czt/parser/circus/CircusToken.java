/*
  Copyright (C) 2006 Leo Freitas
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

package net.sourceforge.czt.parser.circus;

import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.parser.util.Token;

public enum CircusToken
  implements Token
{
  CHANNEL(ZString.ZED + ZString.SPACE + CircusString.CIRCCHAN),
  CHANNEL_FROM(ZString.ZED + ZString.SPACE + CircusString.CIRCCHANFROM),
  CHANNEL_SET(ZString.ZED + ZString.SPACE + CircusString.CIRCCHANSET),  
  PROCESS(ZString.ZED + ZString.SPACE + CircusString.CIRCPROC),
  GENPROCESS(ZString.ZED + ZString.SPACE + "generic-process"),
  CIRCSTATE(CircusString.CIRCSTATE + ZString.SPACE),
  CIRCDEF(ZString.SPACE + CircusString.CIRCDEF),
  NAME_SET(ZString.ZED + ZString.SPACE + CircusString.CIRCNAMESET),
  CIRCIF(ZString.IF + ZString.SPACE),
  CIRCELSE(CircusString.CIRCELSE + ZString.SPACE),
  CIRCFI(ZString.SPACE + CircusString.CIRCFI),
  CIRCDO(CircusString.CIRCDO + ZString.SPACE),  
  CIRCOD(ZString.SPACE + CircusString.CIRCOD),  
  CIRCASSIGN(ZString.SPACE + ZString.COLON + ZString.EQUALS + ZString.SPACE),
  CIRCVAR(CircusString.CIRCVAR + ZString.SPACE),
  CIRCVAL(CircusString.CIRCVAL + ZString.SPACE),
  CIRCRES(CircusString.CIRCRES + ZString.SPACE),
  CIRCVRES(CircusString.CIRCVRES + ZString.SPACE),
  CIRCBEGIN(CircusString.CIRCBEGIN + ZString.SPACE),
  CIRCEND(CircusString.CIRCEND + ZString.SPACE);

  private String spelling_;

  CircusToken(String spelling)
  {
    spelling_ = spelling;
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
}
