/**
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.scanner;

import junit.framework.*;

import net.sourceforge.czt.util.ZString;

/**
 * An abstract test class for testing latex to unicode converter.
 */
public abstract class AbstractLatexToUnicodeTest
  extends TestCase
{
  private static final String SPACE = ZString.SPACE;

  /**
   * Checks whether the tranformer transforms
   * the latex string <code>in</code>
   * into the unicode string <code>out</code>.
   */
  protected abstract void transforms(String in, String out);

  public void testHardSpace()
  {
    transforms("~", SPACE);
    transforms("\\,", SPACE);
    transforms("\\:", SPACE);
    transforms("\\;", SPACE);
    transforms("\\ ", SPACE);
    transforms("\\\\", "\n");
    transforms("\\tl", SPACE);
    transforms("\\t2", SPACE);
    transforms("\\t3", SPACE);
    transforms("\\t4", SPACE);
    transforms("\\t5", SPACE);
    transforms("\\t6", SPACE);
    transforms("\\t7", SPACE);
    transforms("\\t8", SPACE);
    transforms("\\t9", SPACE);
    transforms("\\also", "\n");
    transforms("\\znewpage", "\n");
  }

  public void testSpecialCharacters()
  {
    transforms("\\_", "_");
    transforms("\\{", "{");
    transforms("\\}", "}");
    transforms("\\ldata", ZString.LDATA);
    transforms("\\rdata", ZString.RDATA);
    transforms("\\lblot", ZString.LBIND);
    transforms("\\rblot", ZString.RBIND);
  }

  public void testSymbolCharacters()
  {
    transforms("\\vdash", ZString.VDASH);
    transforms("\\land", SPACE + ZString.AND + SPACE);
    transforms("\\lor", SPACE + ZString.OR + SPACE);
    transforms("\\implies", SPACE + ZString.IMP + SPACE);
    transforms("\\iff", SPACE + ZString.IFF + SPACE);
    transforms("\\lnot", ZString.NOT + SPACE);
    transforms("\\forall", ZString.ALL + SPACE);
    transforms("\\exists", ZString.EXI + SPACE);
    transforms("\\cross", SPACE + ZString.CROSS + SPACE);
    transforms("\\in", SPACE + ZString.MEM + SPACE);
    transforms("\\hide", SPACE + ZString.ZHIDE + SPACE);
    transforms("\\project", SPACE + ZString.ZPROJ + SPACE);
    transforms("\\semi", SPACE + ZString.ZCOMP + SPACE);
    transforms("\\pipe", SPACE + ZString.ZPIPE + SPACE);
  }

  public void testPrechar()
  {
    transforms("\\power S",
               ZString.POWER + SPACE + "S");
    transforms("{\\power}S",
               ZString.POWER + "S");
  }

  public void testInchar()
  {
    transforms("\\subseteq",
               SPACE + ZString.SUBSETEQ + SPACE);
    transforms("\\subseteq_1",
               SPACE + ZString.SUBSETEQ + ZString.SUB1 + SPACE);
    transforms("\\subseteq~_1",
               SPACE + ZString.SUBSETEQ + SPACE + SPACE + ZString.SUB1);
    transforms("{\\subseteq}",
               ZString.SUBSETEQ);
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.1 on page 81.
   */
  public void testGreekLetters()
  {
    transforms("\\Delta  S",
               ZString.DELTA + "S");
    transforms("\\Delta~S",
               ZString.DELTA + SPACE + "S");
    transforms("\\lambda x",
               ZString.LAMBDA + SPACE + "x");
    transforms("{\\lambda}x",
               ZString.LAMBDA + "x");
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.3 on page 82.
   */
  public void testSubscriptsAndSuperscripts()
  {
    transforms("x^1",
               "x" + ZString.SUP1);
    transforms("x^{1}",
               "x" + ZString.SUP1);
    transforms("x^\\Delta",
               "x" + ZString.NE + ZString.DELTA + ZString.SW);
    transforms("x^{\\Delta S}",
               "x" + ZString.NE + ZString.DELTA + "S" + ZString.SW);
    /** SPACES are missing in Z standard **/
    transforms("\\exists_1",
               ZString.EXI + ZString.SUB1 + SPACE);
    transforms("\\exists_{1}",
               ZString.EXI + ZString.SUB1 + SPACE);
    transforms("\\exists_\\Delta",
               ZString.EXI + ZString.SE + ZString.DELTA + ZString.NW + SPACE);
    transforms("\\exists_{\\Delta S}",
               ZString.EXI + ZString.SE + ZString.DELTA + "S"
               + ZString.NW + ZString.SPACE);
    transforms("x_a^b",
               "x" + ZString.SE + "a" + ZString.NW
               + ZString.NE + "b" + ZString.SW);
    transforms("x_{a^b}",
               "x" + ZString.SE + "a"
               + ZString.NE + "b" + ZString.SW + ZString.NW);
    transforms("x_a{}_b",
               "x" + ZString.SE + "a" + ZString.NW
               + ZString.SE + "b" + ZString.NW);
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.4 Example 1 on page 83.
   */
  public void testPlusSign()
  {
    transforms("x+y", "x + y");
    transforms("x{+}y", "x+y");
    transforms("x +_1 y",
               "x +" + ZString.SUB1 + " y");
    transforms("x^+",
               "x" + ZString.NE + "+" + ZString.SW);
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.4 Example 2 on page 83.
   */
  public void testRelations()
  {
    transforms("x=y", "x = y");
    transforms("x==y", "x == y");
    transforms("x::=y", "x ::= y");
    transforms("x{=}y", "x=y");
    transforms("x =_1 y", "x =" + ZString.SUB1 + " y");
    transforms("x^=", "x" + ZString.NE + "=" + ZString.SW);
    transforms("x= =y", "x == y");
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.5 on page 84.
   */
  public void testCorewords()
  {
    transforms("\\IF \\disjoint a \\THEN x = y \\mod z \\ELSE x = y \\div z",
               "if disjoint a then x = y mod z else x = y div z");
  }
}
