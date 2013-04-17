/*
  Copyright (C) 2006, 2007 Petra Malik
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
import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

/**
 * An enumeration of Z tokens.
 */
public enum ZToken
  implements Token
{
  TEXT(NewlineCategory.NEITHER),
  DECORWORD(NewlineCategory.NEITHER),
  NUMERAL(NewlineCategory.NEITHER),
  NUMSTROKE(NewlineCategory.NEITHER),
  INSTROKE(ZString.INSTROKE, NewlineCategory.NEITHER),
  OUTSTROKE(ZString.OUTSTROKE, NewlineCategory.NEITHER),
  NEXTSTROKE(ZString.PRIME, NewlineCategory.NEITHER),
  LPAREN(ZString.LPAREN, NewlineCategory.AFTER),
  RPAREN(ZString.RPAREN, NewlineCategory.BEFORE),
  LSQUARE(ZString.LSQUARE, NewlineCategory.AFTER),
  RSQUARE(ZString.RSQUARE, NewlineCategory.BEFORE),
  LBRACE(ZString.LBRACE, NewlineCategory.AFTER),
  RBRACE(ZString.RBRACE, NewlineCategory.BEFORE),
  LBIND(ZString.LBIND, NewlineCategory.AFTER),
  RBIND(ZString.RBIND, NewlineCategory.BEFORE),
  LDATA(ZString.LDATA, NewlineCategory.BOTH),
  RDATA(ZString.RDATA, NewlineCategory.BEFORE), // nl cat BOTH in Standard!
  ZED(ZString.ZED, NewlineCategory.AFTER),
  AX(ZString.AX, NewlineCategory.AFTER),
  SCH(ZString.SCH, NewlineCategory.AFTER),
  GENAX(ZString.GENAX, NewlineCategory.AFTER),
  GENSCH(ZString.GENSCH, NewlineCategory.AFTER),
  END(ZString.END, NewlineCategory.BEFORE),
  NL(ZString.NL, null),
  INDENT(ZString.SPACE, null),

  /*
  ZSTATE(ZString.ZSTATE, NewlineCategory.NEITHER),
  ZSTINIT(ZString.ZSTINIT, NewlineCategory.NEITHER),
  ZSTFIN(ZString.ZSTFIN, NewlineCategory.NEITHER),

  ZASTATE(ZString.ZASTATE, NewlineCategory.NEITHER),
  ZASTINIT(ZString.ZASTINIT, NewlineCategory.NEITHER),
  ZASTFIN(ZString.ZASTFIN, NewlineCategory.NEITHER),

  ZCSTATE(ZString.ZCSTATE, NewlineCategory.NEITHER),
  ZCSTINIT(ZString.ZCSTINIT, NewlineCategory.NEITHER),
  ZCSTFIN(ZString.ZCSTFIN, NewlineCategory.NEITHER),

  ZRETRIEVE(ZString.ZRETRIEVE, NewlineCategory.NEITHER),
  ZRETRIEVEIN(ZString.ZRETRIEVEIN, NewlineCategory.NEITHER),
  ZRETRIEVEOUT(ZString.ZRETRIEVEOUT, NewlineCategory.NEITHER),

  ZAINITIN(ZString.ZAINITIN, NewlineCategory.NEITHER),
  ZAFINOUT(ZString.ZAFINOUT, NewlineCategory.NEITHER),
  ZCINITIN(ZString.ZCINITIN, NewlineCategory.NEITHER),
  ZCFINOUT(ZString.ZCFINOUT, NewlineCategory.NEITHER),

  ZFSREFINES(ZString.ZFSREFINES, NewlineCategory.NEITHER),
  ZBSREFINES(ZString.ZBSREFINES, NewlineCategory.NEITHER)
*/
  ;
  private String spelling_;
  private NewlineCategory newlineCategory_;

  ZToken(NewlineCategory newlineCategory)
  {
    newlineCategory_ = newlineCategory;
  }

  ZToken(String spelling, NewlineCategory newlineCategory)
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
