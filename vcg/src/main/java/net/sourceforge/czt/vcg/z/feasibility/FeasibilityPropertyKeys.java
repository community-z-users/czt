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
package net.sourceforge.czt.vcg.z.feasibility;

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
public interface FeasibilityPropertyKeys extends VCGPropertyKeys {

  /**
   * When this property is <code>true</code>, the VCG will
   * add VC predicates to ensure given sets are non-empty.
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS =
    "vcg_fsb_add_givenset_vcs";

  /**
   * When creating precondition for Z schemas, could generate VC as a
   * flat list of compact Z Schemas. Default=false (e.g., Non-Z tool friendly!)
   */
  String PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS =
    "vcg_fsb_create_zschemas";


  // default values from properties in VCGPropertyKeys
  boolean PROP_VCG_FEASIBILITY_PROCESS_PARENTS_DEFAULT         = false;
  boolean PROP_VCG_FEASIBILITY_ADD_TRIVIAL_VC_DEFAULT          = false;
  boolean PROP_VCG_FEASIBILITY_APPLY_TRANSFORMERS_DEFAULT      = true;
  boolean PROP_VCG_FEASIBILITY_RAISE_TYPE_WARNINGS_DEFAULT     = true; /* by default raise warnings as errors */
  Markup  PROP_VCG_FEASIBILITY_PREFERRED_MARKUP_DEFAULT        = Markup.LATEX;
  String  PROP_VCG_FEASIBILITY_PARENTS_TO_IGNORE_DEFAULT       = null;

  // new default values
  boolean PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS_DEFAULT      = true;
  boolean PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS_DEFAULT       = false;

  // Feasibility toolkit name
  String VCG_FEASIBILITY_TOOLKIT_NAME = "fsb_toolkit";

  // Feasibility Z State Markup directives
  // %%Zword \zstate zstate
  // %%Zword \zstinit zstinit
  //
  // They are used to tag the user specification schema
  // as the chosen state and state initialisation ones.
  // There should only be one, and cmd-line options might
  // override this choice encoded in the user ZSect itself.
  String VCG_FEASIBILITY_STATE_LMARKUP      = "\\zstate";
  String VCG_FEASIBILITY_STATE_UMARKUP      = "zstate";
  String VCG_FEASIBILITY_STATE_INIT_LMARKUP = "\\zstinit";
  String VCG_FEASIBILITY_STATE_INIT_UMARKUP = "zstinit";

  // Pre ZSection suffix (e.g., ZSect foo -> ZSect foo_pre)
  // Pre ZSection conjecture names N_vc_pre
  String VCG_FEASIBILITY_SOURCENAME_SUFFIX = "_fsb";
  String VCG_FEASIBILITY_VCNAME_SUFFIX     = "_vc_fsb";
}
