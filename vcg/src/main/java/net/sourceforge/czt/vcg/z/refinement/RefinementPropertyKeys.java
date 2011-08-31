/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z.refinement;

import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.vcg.z.VCGPropertyKeys;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public interface RefinementPropertyKeys extends VCGPropertyKeys
{
  String PROP_VCG_REFINEMENT_CREATE_ZSCHEMAS =
         "vcg_ref_create_zschemas" ;

  String VCG_REFINEMENT_SOURCENAME_SUFFIX = "_ref";
  String VCG_REFINEMENT_VCNAME_SUFFIX = "_vc_ref";

  // Refinement toolkit name
  String VCG_REFINEMENT_TOOLKIT_NAME = "ref_toolkit";


  // default values from properties in VCGPropertyKeys
  boolean PROP_VCG_REFINEMENT_PROCESS_PARENTS_DEFAULT         = false;
  boolean PROP_VCG_REFINEMENT_ADD_TRIVIAL_VC_DEFAULT          = false;
  boolean PROP_VCG_REFINEMENT_APPLY_TRANSFORMERS_DEFAULT      = true;
  boolean PROP_VCG_REFINEMENT_RAISE_TYPE_WARNINGS_DEFAULT     = true; /* by default raise warnings as errors */
  Markup  PROP_VCG_REFINEMENT_PREFERRED_MARKUP_DEFAULT        = Markup.LATEX;
  String  PROP_VCG_REFINEMENT_PARENTS_TO_IGNORE_DEFAULT       = "";
  String  PROP_VCG_REFINEMENT_ZSTATE_NAME_DEFAULT             = "";

  // new default values
  boolean PROP_VCG_REFINEMENT_ADD_GIVENSET_VCS_DEFAULT      = true;
  boolean PROP_VCG_REFINEMENT_CREATE_ZSCHEMAS_DEFAULT       = true;
}
