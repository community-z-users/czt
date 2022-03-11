/*
  Copyright (C) 2004, 2006 Petra Malik
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

/**
 * Symbols used by the latex to unicode scanner.
 *
 * @author Petra Malik
 */
public enum LatexSym
  implements Token
{
  /**
   * Narrative text.
   */
  TEXT,

  /**
   * Just a Z unicode string.
   */
  UNICODE,

  /**
   * A complete %%Zchar directive.
   * It goes until the end of the line.
   */
  CHAR_MARKUP,

  /**
   * A %%Zinword directive.
   * It starts a directive command.
   */
  INWORD_MARKUP,

  /**
   * A %%Zpreword directive.
   * It starts a directive command.
   */
  PREWORD_MARKUP,

  /**
   * A %%Zpostword directive.
   * It starts a directive command.
   */
  POSTWORD_MARKUP,

  /**
   * The name of a latex command defined in a directive.
   */
  NAME,

  /**
   * The end of a markup directive.
   */
  END_MARKUP,

  /**
   * A %%Zword directive.
   */
  WORD_MARKUP,

  /**
   * The begin of a section header.
   */
  SECT,

  /**
   * The end of a section header or Z paragraph.
   */
  END,

  /**
   * The section keyword.
   */
  SECTION,

  /**
   * The parents keyword.
   */
  PARENTS,

  /**
   * Part of a (Z/EVES) proof keyword
   */
  PROOFWORD,

  /**
   * Part of a (Z/EVES) predicate label
   */
  ZEVESLABEL;

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
    return null;
  }
}
