/**
Copyright 2003 Tim Miller
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.parser.oz;

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

/**
 * Methods for extracting strokes from names
 */
public class Strokes
{
  /** The regular expressions for a number strokes */
  public final static String NUMSTROKE_REGEX = 
    ZString.SE + "[0-9]"  + ZString.NW;

  //the ZFactory to create the DeclName
  private static ZFactory zFactory_ = new ZFactoryImpl();

  //temporary: replace latex word glue with unicode
  public static String replace(String word)
  {
    String name = new String(word);
    if (name.indexOf("_{") >= 0) {
      name = name.replaceAll("\\}", ZString.NW);
    }
    if (name.indexOf("^{") >= 0) {
      name = name.replaceAll("\\}", ZString.SW);
    }
    name = name.replaceAll("_\\{", ZString.SE);
    name = name.replaceAll("^\\{", ZString.NE);
    name = name.replaceAll("!", ZString.OUTSTROKE);
    name = name.replaceAll("\\?", ZString.INSTROKE);
    name = name.replaceAll("'", ZString.PRIME);
    return name;
  }
  /**
   * Returns DeclName object with the strokes extracted into the 
   * DeclName's list of strokes
   */  
  public static DeclName getWordAndStroke(String name)
  {
    DeclName result = null;
    String baseName = null;
    List strokes = new ArrayList();

    int finalStroke = name.length();

    for (int i = name.length() - 1;
	 i >= 0 &&
           (name.charAt(i) == ZChar.INSTROKE ||
            name.charAt(i) == ZChar.OUTSTROKE ||
            name.charAt(i) == ZChar.PRIME ||
            (i >= 2 &&
             name.substring(i - 2, i + 1).matches(NUMSTROKE_REGEX)));
	 i--) {

      if (name.charAt(i) == ZChar.INSTROKE ||
          name.charAt(i) == ZChar.OUTSTROKE ||
          name.charAt(i) == ZChar.PRIME) {
	strokes.add(0, getStroke(name.substring(i, i + 1)));
      }
      else {
	strokes.add(0, getNumStroke(name.substring(i - 2, i + 1)));
	i -= 2;  //skip the rest
      }
      finalStroke = i;
    }

    baseName = name.substring(0, finalStroke);

    result = zFactory_.createDeclName(baseName, strokes, null);
    return result;
  }

  /**
   * Returns the symbol number for a given stroke
   */
  private static Stroke getStroke(String stroke)
    throws CztException
  {
    Stroke result = null;

    switch (stroke.charAt(0))
    {
      case ZChar.INSTROKE:
        result = zFactory_.createInStroke();
        break;
      case ZChar.OUTSTROKE:
        result = zFactory_.createOutStroke();
        break;
      case ZChar.PRIME:
        result = zFactory_.createNextStroke();
        break;
      default:        
        throw new CztException("No matching stroke");
    }
    return result;
  }

  /**
   * Returns the symbol number for a given number stroke
   */
  protected static NumStroke getNumStroke(String stroke)
  {
    NumStroke result = null;

    switch (stroke.charAt(0))
    {
      case ZChar.SE:
        result = 
	  zFactory_.createNumStroke(new Integer(stroke.substring(1, 2)));
        break;
      default:
        throw new CztException("No matching number stroke");
    }
    return result;
  }
}
