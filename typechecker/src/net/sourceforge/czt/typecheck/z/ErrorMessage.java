/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

/**
 * An enumeration of type errors.
 */
public enum ErrorMessage
{
  ERROR_FILE_LINE,
  ERROR_FILE_LINE_COL,
  NO_LOCATION,
  TYPE_MISMATCH_IN_MEM_PRED,
  TYPE_MISMATCH_IN_REL_OP,
  TYPE_MISMATCH_IN_EQUALITY,
  TYPE_MISMATCH_IN_CHAIN_REL,
  NON_SCHEXPR_IN_EXPR_PRED,
  TYPE_MISMATCH_IN_SIGNATURE,
  REDECLARED_SECTION,
  REDECLARED_PARENT,
  SELF_PARENT,
  REDECLARED_GLOBAL_NAME,
  STROKE_IN_GIVEN,
  STROKE_IN_GEN,
  REDECLARED_GEN,
  NON_SET_IN_FREETYPE,
  PARAMETERS_NOT_DETERMINED,
  PARAMETER_MISMATCH,
  UNDECLARED_IDENTIFIER,
  NON_SET_IN_DECL,
  NON_SCHEXPR_IN_INCLDECL,
  NON_SET_IN_INSTANTIATION,
  NON_SET_IN_POWEREXPR,
  NON_SET_IN_PRODEXPR,
  TYPE_MISMATCH_IN_SET_EXPR,
  INDEX_ERROR_IN_TUPLESELEXPR,
  NON_PRODTYPE_IN_TUPLESELEXPR,
  NON_SCHEXPR_IN_QNT1EXPR,
  NON_SCHEXPR_IN_SCHEXPR2,
  TYPE_MISMATCH_IN_CONDEXPR,
  NON_SCHEXPR_IN_HIDE_EXPR,
  NON_EXISTENT_NAME_IN_HIDEEXPR,
  NON_SCHEXPR_IN_PREEXPR,
  NON_FUNCTION_IN_APPLEXPR,
  TYPE_MISMATCH_IN_APPLEXPR,
  NON_SCHEXPR_IN_THETAEXPR,
  NON_SCHEXPR_IN_DECOREXPR,
  NON_SCHEXPR_IN_RENAMEEXPR,
  DUPLICATE_NAME_IN_RENAMEEXPR,
  NON_BINDING_IN_BINDSELEXPR,
  NON_EXISTENT_SELECTION,
  DUPLICATE_IN_BINDEXPR,
}
