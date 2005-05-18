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
package net.sourceforge.czt.typecheck.oz;

/**
 * An enumeration of type errors.
 */
public enum ErrorMessage
{
  NON_CLASS_IN_CLASSUNIONEXPR,
  INCOMPATIBLE_FEATURE_IN_CLASSUNIONEXPR,
  INCOMPATIBLE_OP_IN_CLASSUNIONEXPR,
  NON_REF_IN_POLYEXPR,
  PARAMETER_MISMATCH_IN_POLYEXPR,
  NON_CLASS_IN_OPPROMEXPR,
  NON_EXISTENT_NAME_IN_OPPROMEXPR,
  OP_NOT_VISIBLE_IN_OPPROMEXPR,
  NON_CLASS_INHERITED,
  NON_PRIMDECL_IN_DELTALIST,
  REDECLARED_NAME_IN_CLASSPARA,
  INCOMPATIBLE_OVERRIDING,
  INCOMPATIBLE_OP_OVERRIDING,
  NON_BINDING_IN_BINDSELEXPR,
  NON_EXISTENT_SELECTION,
  NON_SCHEXPR_IN_RENAMEEXPR,
  TYPE_MISMATCH_IN_OPEXPR2,
  TYPE_MISMATCH_IN_SEQOPEXPR,
  TYPE_MISMATCH_IN_PARALLELOPEXPR,
  DUPLICATE_NAME_IN_RENAMEOPEXPR
}
