/*
  Copyright (C) 2006 Petra Malik
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

import net.sourceforge.czt.z.util.WarningManager;

/**
 * <P>Contains String constants for the keys used in parse properties.</P>
 *
 * <P>The behaviour of the CZT parser utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the parser utilities.</P>
 *
 * @author Petra Malik
 */
public interface TypecheckPropertiesKeys
{
  String PROP_TYPECHECK_DEBUG =
    "typecheck_debug";

  /** When this property is <code>true</code>, the typechecker
   *  will allow variable use before declaration.
   */
  String PROP_TYPECHECK_USE_BEFORE_DECL = 
    "typecheck_use_before_decl";

  
  /** When this property is <code>true</code>, the typechecker
   *  will allow recursive types.
   */
  String PROP_TYPECHECK_RECURSIVE_TYPES =
    "typecheck_recursive_types";

  
  /** 
   *  When this property is <code>true</code>, the typechecker
   *  will alphabetically sort names in declaration lists. That is, 
   *  names in VarDecl, and IncDecl within DeclLists, etc.
   */
  String PROP_TYPECHECK_SORT_DECL_NAMES =
    "typecheck_sort_decl_names";  
  
  String PROP_TYPECHECK_USE_NAMEIDS =
    "typecheck_use_nameids";

  String PROP_TYPECHECK_WARNINGS_OUTPUT =
    "typecheck_raise_warnings";  
  
  String PROP_TYPECHECK_SUMMARY_INCLUDE_PARENTS = "typecheck_summary_incl_parents";
  String PROP_TYPECHECK_SUMMARY_INCLUDE_STDSECTS = "typecheck_summary_incl_stdsects";

  boolean PROP_TYPECHECK_DEBUG_DEFAULT           = false;
  boolean PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT = false;
  boolean PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT = false;
  boolean PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT = false;
  boolean PROP_TYPECHECK_USE_NAMEIDS_DEFAULT     = false;  
  WarningManager.WarningOutput PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT = WarningManager.WarningOutput.SHOW;

  boolean PROP_TYPECHECK_SUMMARY_INCLUDE_PARENTS_DEFAULT = true;
  boolean PROP_TYPECHECK_SUMMARY_INCLUDE_STDSECTS_DEFAULT = false;
}
