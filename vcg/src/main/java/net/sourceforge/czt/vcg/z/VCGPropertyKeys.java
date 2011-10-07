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
package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.session.Markup;

/**
 * <P>Contains String constants for the keys used in VCG properties.</P>
 *
 * <P>The behaviour of the CZT VCG utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the VCG utilities.</P>
 *
 * @author Leo Freitas
 */
public interface VCGPropertyKeys {

  /* VCG CLASSES PROPERTIES */

  /** 
   * When this property is <code>true</code>, the VCG will
   * process all the parent sections of the section being
   * processed, except for those set to be ignored. By default
   * we always check them. Other tools might like to change this
   * for common sections like toolkits.
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_VCG_PROCESS_PARENTS =
    "vcg_process_parents";
  
  /**
   * When this property is <code>true</code>, the VCG will
   * add trivial (true, \forall x @ true and true) VCG predicates.
   * Other tools might want to avoid adding these, or indeed applying
   * predicate transformers over them. By default we keep them.
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_VCG_ADD_TRIVIAL_VC =
    "vcg_add_trivial_vc";

  /**
   * When processing parent sections, it is useful to avoid certain
   * parents, like toolkits, which have stable / discharged VCs. This
   * property represents a list of such parents to ignore. Each VCG tool
   * should have its own default list - e.g., in general, we ignore nothing.
   *
   * DEFAULT = null; TYPE = String (e.g., separated by SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR)
   */
  String PROP_VCG_PARENTS_TO_IGNORE =
    "vcg_parents_to_ignore";

  /**
   * Each VCG tool could apply term transformers to generated VCs.
   * Obviously, each tool is responsible then for transformation soundness.
   * For instance, domain check VCs have this as true, where VCs like
   * (true and true) or (false or true) becomes true.
   *
   * DEFAULT = false; TYPE = Boolean
   */
  String PROP_VCG_APPLY_TRANSFORMERS =
    "vcg_apply_transformers";

  /**
   * Each processed section produce, for each VC kind being generated, a
   * new ZSection with its owner as a parent, where VCs reside. This gets
   * type checked during VCG, and type errors are always raised (e.g.,
   * generated VCs ought not to have type errors). Moreover, during type
   * checking warnings might also appear. This flag determines whether
   * such type warnings should be raised as errors or not.
   * DEFAULT = true; TYPE = Boolean
   */
  //TODO: use Typechecker's value instead? Why override it? (Leo)
  String PROP_VCG_RAISE_TYPE_WARNINGS =
    "vcg_raise_type_warnings";

  /**
   * Checks definition table information is consistent according to
   * the <code>checkOverallConsistency()</code> method.
   */
  String PROP_VCG_CHECK_DEFTBL_CONSISTENCY =
    "vcg_check_deftbl_consistency";

  boolean PROP_VCG_PROCESS_PARENTS_DEFAULT         = true;
  boolean PROP_VCG_APPLY_TRANSFORMERS_DEFAULT      = false;
  boolean PROP_VCG_ADD_TRIVIAL_VC_DEFAULT          = true;
  boolean PROP_VCG_RAISE_TYPE_WARNINGS_DEFAULT     = false; 
  boolean PROP_VCG_CHECK_DEFTBL_CONSISTENCY_DEFAULT= true;
  String  PROP_VCG_PARENTS_TO_IGNORE_DEFAULT       = null;

  /* VCG UTILITY CLASS PROPERTIES */

  /**
   * Top-level utility classes should print benchmark times for various
   * activities like parsing, type checking, and VCG times per file.
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_VCGU_PRINT_BENCHMARK =
    "vcgu_print_benchmark";

  // Use LatexPrinterPropertyKeys.PROP_LATEXPRINTER_WRAPPING
  //String PROP_VCGU_LATEX_OUTPUT_WRAPPING =
  //  "vcgu_latex_output_wrapping";

  /**
   * When generating VCs from the AST in memory, we will use CZT printers.
   * Those usually support various Markups. This flag determines preferred
   * markup for output.
   * DEFAULT = LaTeX; TYPE = Markup
   */
  String PROP_VCGU_PREFERRED_OUTPUT_MARKUP =
    "vcgu_preferred_markup";

  boolean PROP_VCGU_PRINT_BENCHMARK_DEFAULT         = true;
  boolean PROP_VCGU_LATEX_OUTPUT_WRAPPING_DEFAULT   = true;
  Markup  PROP_VCGU_PREFERRED_MARKUP_DEFAULT        = Markup.LATEX;
  
}
