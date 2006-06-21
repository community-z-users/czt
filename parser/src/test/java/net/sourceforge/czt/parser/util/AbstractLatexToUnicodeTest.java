/*
  Copyright 2003, 2006 Petra Malik
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

import junit.framework.*;

import net.sourceforge.czt.z.util.ZString;

/**
 * An abstract test class for testing latex to unicode converter.
 */
public abstract class AbstractLatexToUnicodeTest
  extends TestCase
{
  private static final String SPACE = ZString.SPACE;

  /**
   * Checks whether the tranformer transformsZed
   * the latex string <code>in</code>
   * into the unicode string <code>out</code>.
   */
  protected abstract void transforms(String in, String out)
    throws Exception;

  protected void transformsZed(String in, String out)
    throws Exception
  {
    transforms("\\begin{zed}" + in + "\\end{zed}",
               ZString.ZED + out + ZString.END);
  }

  public void testHardSpace()
    throws Exception
  {
    transformsZed("~", SPACE);
    transformsZed("\\,", SPACE);
    transformsZed("\\:", SPACE);
    transformsZed("\\;", SPACE);
    transformsZed("\\ ", SPACE);
    transformsZed("\\\\", ZString.NL);
    transformsZed("\\t1", SPACE);
    transformsZed("\\t2", SPACE);
    transformsZed("\\t3", SPACE);
    transformsZed("\\t4", SPACE);
    transformsZed("\\t5", SPACE);
    transformsZed("\\t6", SPACE);
    transformsZed("\\t7", SPACE);
    transformsZed("\\t8", SPACE);
    transformsZed("\\t9", SPACE);
    transformsZed("\\also", ZString.NL);
    transformsZed("\\znewpage", ZString.NL);
  }

  public void testSpecialCharacters()
    throws Exception
  {
    transformsZed("[", "[");
    transformsZed("]", "]");
    transformsZed("\\_", "_");
    transformsZed("\\{", "{");
    transformsZed("\\}", "}");
    transformsZed("\\ldata", ZString.LDATA);
    transformsZed("\\rdata", ZString.RDATA);
    transformsZed("\\lblot", ZString.LBIND);
    transformsZed("\\rblot", ZString.RBIND);
  }

  public void testSymbolCharacters()
    throws Exception
  {
    transformsZed("\\vdash", ZString.VDASH);
    transformsZed("\\land", SPACE + ZString.AND + SPACE);
    transformsZed("\\lor", SPACE + ZString.OR + SPACE);
    transformsZed("\\implies", SPACE + ZString.IMP + SPACE);
    transformsZed("\\iff", SPACE + ZString.IFF + SPACE);
    transformsZed("\\lnot", ZString.NOT + SPACE);
    transformsZed("\\forall", ZString.ALL + SPACE);
    transformsZed("\\exists", ZString.EXI + SPACE);
    transformsZed("\\cross", SPACE + ZString.CROSS + SPACE);
    transformsZed("\\in", SPACE + ZString.MEM + SPACE);
    transformsZed("\\hide", SPACE + ZString.ZHIDE + SPACE);
    transformsZed("\\project", SPACE + ZString.ZPROJ + SPACE);
    transformsZed("\\semi", SPACE + ZString.ZCOMP + SPACE);
    transformsZed("\\pipe", SPACE + ZString.ZPIPE + SPACE);
  }

  public void testPrechar()
    throws Exception
  {
    String result = ZString.POWER + SPACE + "S";
    transformsZed("\\power S", result);
    transformsZed("\\power\nS", result);
    transformsZed("\\power     S", result);
    transformsZed("\\power\n\n S", result);
    result = ZString.POWER + "S";
    transformsZed("{\\power}S", result);
    transformsZed("   {   \\power   }     S", result);
    transformsZed("\n{\n\\power\n}\n S\n", result);
  }

  public void testInchar()
    throws Exception
  {
    transformsZed("\\subseteq",
               SPACE + ZString.SUBSETEQ + SPACE);
    transformsZed("\\subseteq_1",
               SPACE + ZString.SUBSETEQ + ZString.SUB1 + SPACE);
    transformsZed("\\subseteq~_1",
               SPACE + ZString.SUBSETEQ + SPACE + SPACE + ZString.SUB1);
    transformsZed("{\\subseteq}",
               ZString.SUBSETEQ);
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.1 on page 81.
   */
  public void testGreekLetters()
    throws Exception
  {
    transformsZed("\\Delta  S",
               ZString.DELTA + "S");
    transformsZed("\\Delta~S",
               ZString.DELTA + SPACE + "S");
    transformsZed("\\lambda x",
               ZString.LAMBDA + SPACE + "x");
    transformsZed("{\\lambda}x",
               ZString.LAMBDA + "x");
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.3 on page 82.
   */
  public void testSubscriptsAndSuperscripts()
    throws Exception
  {
    transformsZed("x^1",
               "x" + ZString.SUP1);
    transformsZed("x^{1}",
               "x" + ZString.SUP1);
    transformsZed("x^\\Delta",
               "x" + ZString.NE + ZString.DELTA + ZString.SW);
    transformsZed("x^{\\Delta S}",
               "x" + ZString.NE + ZString.DELTA + "S" + ZString.SW);
    /** SPACES are missing in Z standard **/
    transformsZed("\\exists_1",
               ZString.EXI + ZString.SUB1 + SPACE);
    transformsZed("\\exists_{1}",
               ZString.EXI + ZString.SUB1 + SPACE);
    transformsZed("\\exists_\\Delta",
               ZString.EXI + ZString.SE + ZString.DELTA + ZString.NW + SPACE);
    transformsZed("\\exists_{\\Delta S}",
               ZString.EXI + ZString.SE + ZString.DELTA + "S"
               + ZString.NW + ZString.SPACE);
    transformsZed("x_a^b",
               "x" + ZString.SE + "a" + ZString.NW
               + ZString.NE + "b" + ZString.SW);
    transformsZed("x_{a^b}",
               "x" + ZString.SE + "a"
               + ZString.NE + "b" + ZString.SW + ZString.NW);
    transformsZed("x_a{}_b",
               "x" + ZString.SE + "a" + ZString.NW
               + ZString.SE + "b" + ZString.NW);
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.4 Example 1 on page 83.
   */
  public void testPlusSign()
    throws Exception
  {
    transformsZed("x+y", "x + y");
    transformsZed("x{+}y", "x+y");
    transformsZed("x +_1 y",
               "x +" + ZString.SUB1 + " y");
    transformsZed("x^+",
               "x" + ZString.NE + "+" + ZString.SW);
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.4 Example 2 on page 83.
   */
  public void testRelations()
    throws Exception
  {
    transformsZed("x=y", "x = y");
    transformsZed("x==y", "x == y");
    transformsZed("x::=y", "x ::= y");
    transformsZed("x{=}y", "x=y");
    transformsZed("x =_1 y", "x =" + ZString.SUB1 + " y");
    transformsZed("x^=", "x" + ZString.NE + "=" + ZString.SW);
    transformsZed("x= =y", "x == y");
  }

  /**
   * Examples taken from
   * Z Standard working draft 2.7
   * chapter A.2.4.5 on page 84.
   */
  public void testCorewords()
    throws Exception
  {
    transformsZed("\\IF \\disjoint a \\THEN x = y \\mod z \\ELSE x = y \\div z",
               "if disjoint a then x = y mod z else x = y div z");
  }

  public void testComments()
    throws Exception
  {
    transformsZed("% ignore \n   te   % ignore \n st  % \\end{zed}\n", "test");
    transformsZed("_% ignore\n1", ZString.SUB1);
  }

  public void testAxiomaticDescription()
    throws Exception
  {
    transforms("\\begin{axdef}\\where\\end{axdef}",
               ZString.AX
               + ZString.SPACE + ZString.VL + ZString.SPACE
               + ZString.END);
  }

  public void testSchemaDefinition()
    throws Exception
  {
    transforms("\\begin{schema}{NAME}\\where\\end{schema}",
               ZString.SCH + "NAME"
               + ZString.SPACE // not necessary
               + ZString.SPACE + ZString.VL + ZString.SPACE
               + ZString.END);
  }

  public void testGenericAxiomaticDescription()
    throws Exception
  {
    transforms("\\begin{gendef}[Formals]\\where\\end{gendef}",
               ZString.AXCHAR + ZString.GENCHAR
               + "[Formals]"
               + ZString.SPACE + ZString.VL + ZString.SPACE
               + ZString.END);
  }

  public void testGenericSchemaDefinition()
    throws Exception
  {
    transforms("\\begin{schema}{NAME}[Formals]\\where\\end{schema}",
               ZString.SCHCHAR + ZString.GENCHAR + "NAME"
               + ZString.SPACE // not necessary
               + "[Formals]"
               + ZString.SPACE + ZString.VL + ZString.SPACE
               + ZString.END);
  }
}
