/*
  Copyright (C) 2005, 2006, 2007 Mark Utting
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
 * Type of definition added to a definition table. This is useful to know
 * wheather one should treat an expression as membership (VarDecl) or equality 
 * (ConstDecl)
 *
 * @author leo
 */
public enum DefinitionType
{
  // used for S == E (i.e. horizontal or schemas)
  CONSTDECL,
  // used for axiomatic boxes
  VARDECL,
  // used for schema boxes from trivial (RefExpr) inclusions
  LOCALDECL,
  // used for complex schema inclusions
  INCLDECL,
}
