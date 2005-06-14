/*
  Copyright (C) 2005 Petra Malik
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
 * An enumeration of possible parse/scan messages, warnings, and
 * errors that may occur during a parse.
 */
public enum ParseMessage
{
  MSG_EXPR_EXPECTED,
  MSG_EXPR_EXPECTED_FOUND_PRED,
  MSG_PRED_EXPECTED,
  MSG_REFNAME_EXPECTED,
  MSG_REFNAME_NO_PARAMS_EXPECTED,
  MSG_UNKNOWN_LATEX_COMMAND,
  MSG_UNMATCHED_BEGIN_END,
  MSG_UNMATCHED_BRACES,
  /**
   * Used when a Z NAME does not have a following NW character for
   * every SE character, or a following SW character for every NE
   * character, or if these do not occur in nested pairs (see also Z
   * Standard, first edition, 7.4.1).
   */
  MSG_UNMATCHED_WORDGLUE,
  MSG_UNEXPECTED_TOKEN,
  MSG_SYNTAX_ERROR,
  MSG_STROKE_IN_OPNAME,
  MSG_OPNAME_AS_DECLWORD,
  MSG_PARENT_NOT_FOUND,
  MSG_OF_PARENT_NOT_FOUND,
  MSG_DUPLICATE_STATE,
  MSG_DUPLICATE_INIT,
  MSG_OPNAME_ERROR,
  MSG_CANNOT_MERGE_OPTABLES,
  MSG_CANNOT_MERGE_JOKERTABLES,
  MSG_CANNOT_ADD_OP,
  MSG_CANNOT_ADD_JOKER;
}
