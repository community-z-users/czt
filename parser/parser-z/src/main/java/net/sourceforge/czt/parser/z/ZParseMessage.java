/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.parser.z;

/**
 * An enumeration of possible parse/scan messages, warnings, and
 * errors that may occur during a parse.
 */
public enum ZParseMessage
{
  MSG_EXPR_EXPECTED ("Expression expected"),
  MSG_EXPR_EXPECTED_FOUND_PRED ("Expression expected; found predicate"),
  MSG_PRED_EXPECTED ("Predicate expected"),
  MSG_OPEXPR_EXPECTED ("Operation expression expected"),
  MSG_REFNAME_EXPECTED ("Reference name expected"),
  MSG_REFNAME_NO_PARAMS_EXPECTED ("Name with no instantiations expected"),
  MSG_UNKNOWN_LATEX_COMMAND ("Unknown latex command {0}"),
  MSG_UNMATCHED_BEGIN_END ("\\end'{'{0}'}' missing"),
  MSG_UNMATCHED_BRACES ("Unmatched braces {0}"),
  MSG_UNMATCHED_WORDGLUE ("Unmatched wordglue {0}", "A NAME does not have a following NW character for every SE character, or a following SW character for every NE character, or these do not occur in nested pairs"),
  MSG_UNEXPECTED_TOKEN ("Unexpected token {0}"),
  MSG_UNEXPECTED_TOKEN_NAME_EXPECTED ("Unexpected token {0}; '{'NAME'}' expected"),
  MSG_SYNTAX_ERROR ("Syntax error at symbol {0}"),
  MSG_STROKE_IN_OPNAME ("Syntax error in operator name {0}", "Names in operator templates cannot contain strokes"),
  MSG_OPNAME_AS_DECLWORD ("{0} is declared as an operator, and cannot be used as a declaration name"),
  MSG_PARENT_NOT_FOUND ("Parent section {0} could not be found"),
  MSG_CYCLIC_PARENT ("Cyclic parents found: {0}"),
  MSG_OF_PARENT_NOT_FOUND ("{0} of parent section {1} could not be found (Command execution error message: {2})"),
  MSG_DUPLICATE_STATE ("Duplicate state declaration"),
  MSG_DUPLICATE_INIT ("Duplicate initial state declaration"),
  MSG_OPNAME_ERROR ("Cannot parse operator name ({0})"),
  MSG_CANNOT_MERGE_OPTABLES ("Cannot merge the parent operator tables ({0})"),
  MSG_CANNOT_MERGE_THMTABLES("Cannot merge the parent named conjecture tables ({0})"),
  MSG_CANNOT_ADD_OP ("Cannot add operator template ({0})"),
  MSG_CANNOT_ADD_THM ("Cannot add named conjecture ({0})"),
  MSG_POSSIBLE_MISSING_SPACE ("Possible missing hard space"),
  MSG_LATEX_COMMAND_DEFINED_TWICE("Command {0} defined twice (in dialect {3}): {1}, {2}"),
  MSG_NOT_WITHIN_SCHBOX("Recognised Z state or refinement relationship {0} schema box.", "The lexer is identifying a Z state or refinement relationship from a part of the specification where it is not allwoed."),

  //MSG_ERROR_REDECLARED_SECTION("Section {0} has been previously declared", "There might be duplicate sections within the file?"),

  //Additional error messages by completing the grammar with error productions
  //wherever possible/purposeful. By Leo
  MSG_MISSING_NL_UNBOXEDPARLIST("Missing hard new-line (i.e. \\\\, \\also, etc.) in unboxed paragraph item list."),
  MSG_SYNTAX_ERROR_IN_VARDECL("Syntax error in variable declaration at token {0}; an expression is expected after token COLON"),
  MSG_SYNTAX_ERROR_IN_SECTION_HEADER("Syntax error in section header");

  private final String message_;
  private final String explanation_;

  ZParseMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  ZParseMessage(String message, String explanation)
  {
    message_ = message;
    explanation_ = explanation;
  }

  String getMessage()
  {
    return message_;
  }

  String getExplanation()
  {
    return explanation_;
  }
}
