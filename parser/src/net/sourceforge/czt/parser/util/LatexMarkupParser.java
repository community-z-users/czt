/*
Copyright 2004 Petra Malik
This file is part of the CZT project: http://czt.sourceforge.net

The CZT project contains free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License as published
by the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License along
with CZT; if not, write to the Free Software Foundation, Inc.,
59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.util;

import java.util.ArrayList;
import java.util.List;

import java_cup.runtime.*;

public class LatexMarkupParser
{
  private Scanner scanner_;

  public LatexMarkupParser(Scanner scanner)
  {
    scanner_ = scanner;
  }

  public List parse()
    throws Exception
  {
    List result = new ArrayList();
    Symbol symbol = scanner_.next_token();
    while (symbol.sym != 0) {
      if (symbol.sym == 3) {
        LatexCommand command = parseMarkupDirective((String) symbol.value);
        if (command != null) result.add(command);
      }
      symbol = scanner_.next_token();
    }
    return result;
  }

  static public LatexCommand parseMarkupDirective(String directive)
  {
    System.out.println("Parse " + directive);
    String[] splitted = directive.split("[ \t]+");
    if (splitted.length == 3) {
      boolean addLeftSpace = false;
      boolean addRightSpace = false;
      String name = splitted[1];
      if ("%%Zprechar".equals(splitted[0])) {
        addRightSpace = true;
      }
      else if ("%%Zpostchar".equals(splitted[0])) {
        addLeftSpace = true;
      }
      else if ("%%Zinchar".equals(splitted[0])) {
        addLeftSpace = true;
        addRightSpace = true;
      }

      if (splitted[2].startsWith("U+")) {
        String hexValue = splitted[2].substring(2, 6);
        int decimal = Integer.parseInt(hexValue, 16);
        // Java 1.4
        char character = Character.forDigit(decimal, 10);
        String unicode = String.valueOf(character);
        // Java 1.5
        //        char[] chars = Character.toChars(decimal);
        //        String unicode = new String(chars);
        return new LatexCommand(name, unicode, addLeftSpace, addRightSpace);
      }
      else {
        System.err.println("WARNING: Cannot parse " + directive);
        System.err.println(splitted[2] + " not supported");
        return null;
      }
    }
    else {
      System.err.println("WARNING: Cannot parse " + directive);
      return null;
    }
  }
}
