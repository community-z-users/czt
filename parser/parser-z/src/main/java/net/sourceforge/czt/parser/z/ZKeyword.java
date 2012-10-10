/*
  Copyright (C) 2006, 2007 Petra Malik
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
import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

/**
 * In the ISO standard, "function", "generic", "relation", and
 * "section" are in the "BOTH" category, but a new line before one of
 * these is possible if multiple paragraphs are permitted inside in
 * a zed paragraph, so have been moved into the "AFTER" category.
 */
public enum ZKeyword
  implements Token
{
  ELSE("else", NewlineCategory.BOTH),
  FALSE("false", NewlineCategory.NEITHER),
  FUNCTION("function", NewlineCategory.AFTER), // nl cat BOTH in the Standard!
  GENERIC("generic", NewlineCategory.AFTER), // nl cat BOTH in the Standard!
  IF("if", NewlineCategory.AFTER),
  LEFTASSOC("leftassoc", NewlineCategory.BOTH),
  LET("let", NewlineCategory.AFTER),
  POWER(ZString.POWER, NewlineCategory.AFTER),
  PARENTS("parents", NewlineCategory.BOTH),
  ZPRE("pre", NewlineCategory.AFTER),
  RELATION("relation", NewlineCategory.AFTER), // nl cat BOTH in the Standard!
  RIGHTASSOC("rightassoc", NewlineCategory.BOTH),
  SECTION("section", NewlineCategory.AFTER), // nl cat BOTH in the Standard!
  THEN("then", NewlineCategory.BOTH),
  /** A CZT extension that allows named conjectures in Unicode. */
  THEOREM(ZString.THEOREM, NewlineCategory.NEITHER),
  TRUE("true", NewlineCategory.NEITHER),
  COLON(ZString.COLON, NewlineCategory.BOTH),
  DEFEQUAL("==", NewlineCategory.BOTH),
  COMMA(ZString.COMMA, NewlineCategory.BOTH),
  DEFFREE("::=", NewlineCategory.BOTH),
  BAR("|", NewlineCategory.BOTH),
  ANDALSO(ZString.AMP, NewlineCategory.BOTH),
  ZHIDE(ZString.ZHIDE, NewlineCategory.BOTH),
  SLASH(ZString.SLASH, NewlineCategory.BOTH),
  DOT(ZString.DOT, NewlineCategory.BOTH),
  SEMICOLON(ZString.SEMICOLON, NewlineCategory.BOTH),
  ARG(ZString.LL, NewlineCategory.AFTER),
  LISTARG(",,", NewlineCategory.BOTH),
  EQUALS(ZString.EQUALS, NewlineCategory.BOTH),
  CONJECTURE(ZString.CONJECTURE, NewlineCategory.BOTH),
  ALL(ZString.ALL, NewlineCategory.AFTER),
  SPOT(ZString.SPOT, NewlineCategory.BOTH),
  EXI(ZString.EXI, NewlineCategory.AFTER),
  EXIONE(ZString.EXIONE, NewlineCategory.AFTER),
  IFF(ZString.IFF, NewlineCategory.BOTH),
  IMP(ZString.IMP, NewlineCategory.BOTH),
  OR(ZString.OR, NewlineCategory.BOTH),
  AND(ZString.AND, NewlineCategory.BOTH),
  NOT(ZString.NOT, NewlineCategory.AFTER),
  MEM(ZString.MEM, NewlineCategory.BOTH),
  ZPROJ(ZString.ZPROJ, NewlineCategory.BOTH),
  CROSS(ZString.CROSS, NewlineCategory.BOTH),
  LAMBDA(ZString.LAMBDA, NewlineCategory.AFTER),
  MU(ZString.MU, NewlineCategory.AFTER),
  THETA(ZString.THETA, NewlineCategory.AFTER),
  ZCOMP(ZString.ZCOMP, NewlineCategory.BOTH),
  ZPIPE(ZString.ZPIPE, NewlineCategory.BOTH)
  ;

  private String spelling_;
  private NewlineCategory newlineCategory_;

  ZKeyword(String spelling, NewlineCategory newlineCategory)
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
