/*
  Copyright (C) 2008 Leo Freitas
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
package net.sourceforge.czt.parser.circusconf;

/**
 *
 * @author leo
 */
public enum WarningMessage {

  WRONG_NUMBER_FIELD_STROKES(
    "Wrong number of fields in communication pattern." +
      "\n\tChannel.: {0}" +
      "\n\tExpected: {1}" +
      "\n\tFound...: {2}" +
      "\n\tSymbol..: {3}" +
      "\n\tLocation: {4}",
    "\n\tThe number of fields in a communication pattern is determined by the right scanning " +
    "of tokens, and a mismatch has been found. That is, there are more ''?'', ''!'', or ''.'' " +
    "than the number of expressions/variable names.");
  
  private final String message_;
  private final String explanation_;
  private boolean flagged_;

  WarningMessage(String message)
  {
    this(message, null);
  }

  WarningMessage(String message, String explanation)
  {    
    message_ = message;
    explanation_ = explanation;
    flagged_ = false;
  }

  String getMessage()
  {
    return message_;
  }

  String getExplanation()
  {
    String result = explanation_;
    flagged_ = true;
    return result;
  }
  
  boolean alreadyFlagged()
  {
    return flagged_;
  }
  
  String getFullMessage()
  {
    String result = getMessage();
    if (!flagged_) result += getExplanation();
    return result;
  }
}
