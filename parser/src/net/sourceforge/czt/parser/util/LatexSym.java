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

package net.sourceforge.czt.parser.util;

/**
 * Symbols used by the latex to unicode scanner.
 */
public class LatexSym
{
  /**
   * End of file.
   */
  public static final int EOF = 0;

  /**
   * Narrative text.
   */
  public static final int TEXT = 1;

  /**
   * Just a Z unicode string.
   */
  public static final int UNICODE = 2;

  /**
   * A complete %%Zchar directive.
   * It goes until the end of the line.
   */
  public static final int CHAR_MARKUP = 3;

  /**
   * A %%Zinword directive.
   * It starts a directive command.
   */
  public static final int INWORD_MARKUP = 31;

  /**
   * A %%Zpreword directive.
   * It starts a directive command.
   */
  public static final int PREWORD_MARKUP = 32;

  /**
   * A %%Zpostword directive.
   * It starts a directive command.
   */
  public static final int POSTWORD_MARKUP = 33;

  /**
   * The name of a latex command defined in a directive.
   */
  public static final int NAME = 34;

  /**
   * The end of a markup directive.
   */
  public static final int END_MARKUP = 35;

  /**
   * A %%Zword directive.
   */
  public static final int WORD_MARKUP = 4;

  /**
   * The begin of a section header.
   */
  public static final int SECT = 5;

  /**
   * The end of a section header or Z paragraph.
   */
  public static final int END = 6;

  /**
   * The section keyword.
   */
  public static final int SECTION = 7;

  /**
   * The parents keyword.
   */
  public static final int PARENTS = 8;
}
