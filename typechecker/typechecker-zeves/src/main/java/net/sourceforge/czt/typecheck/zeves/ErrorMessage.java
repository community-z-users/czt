/*
  Copyright (C) 2006, 2007 Leo Freitas
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
package net.sourceforge.czt.typecheck.zeves;

/**
 * // TODO: use warning manager. think about warnings and better error messages
 * @author Leo Freitas
 */
public enum ErrorMessage 
{

  WITH_NORMALIZATION_NO_CMD,
  USE_CMD_REPL,
  USE_CMD_THMREF,
  USE_CMD_INVALID_REPL,
  SUBST_CMD_PRED_INVOKE,
  SUBST_CMD_BADNAME_INVOKE,
  QNT_CMD_INVALID_INST,
  QNT_CMD_INST,
  APPLY_CMD_THMNAME,
  WITH_CMD_INVALID,
  WITH_CMD_THMNAME,
  BINDEXPR_ERROR_AS_WARNING,
  PRED_ERROR_AS_WARNING,
  UNDECLARED_NAME_ERROR_AS_WARNING//,
  //UNEXPECTED_EXCEPTION_ERROR
          ;

}
