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
package net.sourceforge.czt.dc.z;

import net.sourceforge.czt.session.Markup;

/**
 * <P>Contains String constants for the keys used in parse properties.</P>
 *
 * <P>The behaviour of the CZT parser utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the parser utilities.</P>
 *
 * @author leo
 */
public interface DomainCheckPropertyKeys {

  /** 
   * When this property is <code>true</code>, whenever the domain checker
   * need to create \appliesTo predicates, it uses its infix version. 
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_DOMAINCHECK_USE_INFIX_APPLIESTO =
    "domaincheck_use_infix_appliesto";
  
  /** 
   * When this property is <code>true</code>, the domain checker will
   * process all the parent sections of the section being processed, 
   * except for those set to be ignored.
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_DOMAINCHECK_PROCESS_PARENTS =
    "domaincheck_process_parents";  
  
  /**
   * When this property is <code>false</code>, the domain checker will
   * not add trivial (true) domain check predicates.
   * DEFAULT = false; TYPE = boolean
   */
  String PROP_DOMAINCHECK_ADD_TRIVIAL_DC =
    "domaincheck_add_trivial_dc";
  
  String PROP_DOMAINCHECK_PARENTS_TO_IGNORE =
    "domaincheck_parents_to_ignore";
  
  String PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS =
    "domaincheck_apply_pred_transformers";

  String PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS =
          "domaincheck_raise_type_warnings";

  String PROP_DOMAINCHECK_PREFERED_MARKUP =
          "domaincheck_prefered_markup";

  boolean PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT = true;
  boolean PROP_DOMAINCHECK_PROCESS_PARENTS_DEFAULT = false;
  boolean PROP_DOMAINCHECK_ADD_TRIVIAL_DC_DEFAULT  = false;
  boolean PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT = true;
  boolean PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS_DEFAULT = true; /* by default raise warnings as errors */

  Markup PROP_DOMAINCHECK_PREFERED_MARKUP_DEFAULT = Markup.LATEX;
  String PROP_DOMAINCHECK_PARENTS_TO_IGNORE_DEFAULT = null;
    
  String DOMAIN_CHECK_TOOLKIT_NAME = "dc_toolkit";
  String DOMAIN_CHECK_CONJECTURE_NAME_SUFFIX = "_domainCheck";
  String DOMAIN_CHECK_GENERAL_NAME_SUFFIX = "_dc";
  
}
