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

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.Map;

import java_cup.runtime.Scanner;
import java_cup.runtime.Symbol;

import net.sourceforge.czt.util.CztException;

/**
 * Utilities for handling symbols generated by java_cup.
 */
public final class DebugUtils
{
  /**
   * Do not generate instances of this class.
   */
  private DebugUtils()
  {
  }

  /**
   * Collects all static member variables in a map
   * that maps the value of the variable to its name.
   */
  public static Map getFieldMap(Class aClass)
  {
    Map result = new HashMap();
    Field[] fields = aClass.getFields();
    for (int i = 0; i < fields.length; i++) {
      Field field = fields[i];
      try {
        if (Modifier.isStatic(field.getModifiers())) {
          result.put(field.get(null), field.getName());
        }
      }
      catch (IllegalAccessException e) {
        throw new CztException(e);
      }
    }
    return result;
  }

  public static void scan(Scanner scanner, Class cupSymbolTable)
    throws Exception
  {
    Map symbols = getFieldMap(cupSymbolTable);
    Symbol symbol = null;
    while ((symbol = scanner.next_token()).sym != 0) {
      String symbolName = (String) symbols.get(new Integer(symbol.sym));
      String result = "Token " + symbolName;
      result += " at line " + symbol.left + " column " + symbol.right;
      if (symbol.value != null) {
        String value = symbol.value.toString();
        result += " with value '";
        final int maxLength = 20;
        if (value.length() <= maxLength) {
          result += value + "'";
        }
        else {
          result += value.substring(0, maxLength) + "...'";
        }
      }
      System.out.println(result);
    }
  }
}
