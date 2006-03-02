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

package net.sourceforge.czt.parser.z;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.parser.util.Token;

public enum Keyword
  implements Token
{
  ELSE("else"),
  FALSE("false"),
  FUNCTION("function"),
  GENERIC("generic"),
  IF("if"),
  LEFTASSOC("leftassoc"),
  LET("let"),
  POWERSET(ZString.POWER),
  PARENTS("parents"),
  PRE("pre"),
  RELATION("relation"),
  RIGHTASSOC("rightassoc"),
  SECTION("section"),
  THEN("then"),
  TRUE("true"),
  COLON(ZString.COLON),
  DEFEQUAL("=="),
  COMMA(ZString.COMMA),
  DEFFREE("::="),
  BAR("|"),
  ANDALSO(ZString.AMP),
  HIDE(ZString.ZHIDE),
  RENAME(ZString.SLASH),
  SEMI(ZString.SEMICOLON),
  ARG(ZString.LL),
  LISTARG(",,"),
  EQUALS(ZString.EQUALS);

  private String spelling_;

  Keyword(String spelling)
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
