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

package net.sourceforge.czt.parser.util;

import java.util.Map;

import net.sourceforge.czt.util.ParseException;

import net.sourceforge.czt.z.util.ZChar;

/**
 * @author Petra Malik
 */
public final class LatexMarkupUtils
{
  /**
   * Do not generate instances of this class.
   */
  private LatexMarkupUtils()
  {
  }

  /**
   * @param latexCommands a mapping from unicode strings to latex commands.
   */
  public static LatexCommand uniwordToLatex(String word, Map latexCommands)
    throws ParseException
  {
    LatexCommand command = (LatexCommand) latexCommands.get(word);
    if (command != null) {
      return command;
    }
    String latex = "";
    boolean addLeftSpace = false;
    boolean addRightSpace = false;
    for (int i = 0; i < word.length(); i++) {
      char character = word.charAt(i);
      command = (LatexCommand) latexCommands.get(String.valueOf(character));
      if (command != null) {
        if (command.addLeftSpace() || command.addRightSpace()) {
          latex += "{" + command.getName() + "}";
        }
        else {
          latex += command.getName() + " ";
        }
        addRightSpace = command.addRightSpace();
      }
      else if (character < 256) { // ASCII?
        latex += character;
      }
      else if (ZChar.PRIME == character) {
        latex += "'";
      }
      else {
        String hex = Integer.toString((int) character, 16);
        String message = "Unexpected character " + character
          + " (\\u" + hex + ")";
        throw new ParseException(message, 0, i);
      }
    }
    return new LatexCommand(latex, null, addLeftSpace, addRightSpace);
  }
}
