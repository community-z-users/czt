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
package net.sourceforge.czt.vcg.z.dc;

import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.vcg.z.VCGPropertyKeys;

/**
 * <P>Contains String constants for the keys used in VCG properties.</P>
 *
 * <P>The behaviour of the CZT VCG utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the VCG utilities.</P>
 *
 * @author Leo Freitas
 */
public interface DomainCheckPropertyKeys extends VCGPropertyKeys {

  /** 
   * When this property is <code>true</code>, whenever the domain checker
   * need to create \appliesTo predicates, it uses its infix version. 
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO =
    "vcg_dc_use_infix_appliesto";

  // default values from properties in VCGPropertyKeys
  boolean PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT     = true;
  boolean PROP_VCG_DOMAINCHECK_PROCESS_PARENTS_DEFAULT         = false;
  boolean PROP_VCG_DOMAINCHECK_ADD_TRIVIAL_VC_DEFAULT          = false;
  boolean PROP_VCG_DOMAINCHECK_APPLY_TRANSFORMERS_DEFAULT      = true;
  boolean PROP_VCG_DOMAINCHECK_RAISE_TYPE_WARNINGS_DEFAULT     = false; 
  Markup  PROP_VCG_DOMAINCHECK_PREFERRED_MARKUP_DEFAULT        = Markup.LATEX;
  String  PROP_VCG_DOMAINCHECK_PARENTS_TO_IGNORE_DEFAULT       = null;

  // DC toolkit name
  String VCG_DOMAINCHECK_TOOLKIT_NAME = "dc_toolkit";

  // DC ZSection suffix (e.g., ZSect foo -> ZSect foo_dc)
  // DC ZSection conjecture names N_vc_dc
  String VCG_DOMAINCHECK_SOURCENAME_SUFFIX = "_dc";  // _ on names are with problems :-(
  String VCG_DOMAINCHECK_VCNAME_SUFFIX     = "_vc_dc";
  
  String VCTYPE_DC_DEFAULT = "vc_dc";
}
