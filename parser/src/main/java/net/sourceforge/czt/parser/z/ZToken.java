/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.parser.z;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.parser.util.Token;

/**
 * An enumeration of Z tokens.
 */
public enum ZToken
  implements Token
{
  TEXT,
  DECORWORD,
  NUMERAL,
  NUMSTROKE,
  INSTROKE(ZString.INSTROKE),
  OUTSTROKE(ZString.OUTSTROKE),
  NEXTSTROKE(ZString.PRIME),
  LPAREN(ZString.LPAREN),
  RPAREN(ZString.RPAREN),
  LSQUARE(ZString.LSQUARE),
  RSQUARE(ZString.RSQUARE),
  LBRACE(ZString.LBRACE),
  RBRACE(ZString.RBRACE),
  LBIND(ZString.LBIND),
  RBIND(ZString.RBIND),
  LDATA(ZString.LDATA),
  RDATA(ZString.RDATA),
  ZED(ZString.ZED),
  AX(ZString.AX),
  SCH(ZString.SCH),
  GENAX(ZString.GENAX),
  GENSCH(ZString.GENSCH),
  END(ZString.END),
  NL(ZString.NL);

  private String spelling_;

  ZToken()
  {
  }

  ZToken(String spelling)
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
