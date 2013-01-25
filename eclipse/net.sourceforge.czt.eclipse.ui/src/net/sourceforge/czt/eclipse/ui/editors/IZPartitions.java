/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.editors;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.util.ZEvesString;

/**
 * /**
 * Definition of Z partitioning and its partitions along with their start/end Strings.
 * 
 * @author Chengdong Xu
 */
// TODO: all this is horrible... should reflect ZKeyword and samefor other extensions...
public interface IZPartitions
{

  /**
   * The identifier of the Z partitioning.
   */
  String Z_PARTITIONING = "___z_partitioning"; //$NON-NLS-1$

  /* Definition for LATEX_ZCHAR */
  /**
   * The identifier of the zchar latex partition content type
   * - ZCHAR
   * @value <code>__z_paragraph_latex_zchar</code>
   */
  String Z_PARAGRAPH_LATEX_ZCHAR = "__z_paragraph_latex_zchar"; //$NON-NLS-1$

  /**
   * The start String of the zchar latex partition content type
   * - ZCHAR
   * @value <code>%%zchar</code>
   */
  String Z_PARAGRAPH_LATEX_ZCHAR_START = "%%zchar"; //$NON-NLS-1$

  /* Definition for LATEX_ZED */
  /**
   * The identifier of the latex Z partition content type
   * - ZED
   * @value <code>__z_paragraph_latex_zed</code>
   */
  String Z_PARAGRAPH_LATEX_ZED = "__z_paragraph_latex_zed"; //$NON-NLS-1$

  /* Definition for LATEX_THEOREM */
  /**
   * The identifier of the latex Z theorem paragraph
   * - ZED
   * @value <code>__z_paragraph_latex_theorem</code>
   */
  String Z_PARAGRAPH_LATEX_THEOREM = "__z_paragraph_latex_theorem"; //$NON-NLS-1$

  /**
   * The start String of the latex Z partition content type
   * - ZED
   * @value <code>\\begin{zed}</code>
   */
  String Z_PARAGRAPH_LATEX_ZED_START = "\\begin{zed}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z partition content type
   * - ZED
   * @value <code>\\end{zed}</code>
   */
  String Z_PARAGRAPH_LATEX_ZED_END = "\\end{zed}"; //$NON-NLS-1$

  /* Definition for LATEX_ZSECTION */
  /**
   * The identifier of the latex Z partition content type
   * - Section header markup
   * @value <code>__z_paragraph_latex_zsection</code>
   */
  String Z_PARAGRAPH_LATEX_ZSECTION = "__z_paragraph_latex_zsection"; //$NON-NLS-1$

  /**
   * The start String of the latex Z partition content type
   * - Section header markup
   * @value <code>\\begin{zsection}</code>
   */
  String Z_PARAGRAPH_LATEX_ZSECTION_START = "\\begin{zsection}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z partition content type
   * - Section header markup
   * @value <code>\\end{zsection}</code>
   */
  String Z_PARAGRAPH_LATEX_ZSECTION_END = "\\end{zsection}"; //$NON-NLS-1$

  /* Definition for LATEX_AXDEF */
  /**
   * The identifier of the latex Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>__z_paragraph_latex_axdef</code>
   */
  String Z_PARAGRAPH_LATEX_AXDEF = "__z_paragraph_latex_axdef"; //$NON-NLS-1$

  /**
   * The start String of the latex Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>\\begin{axdef}</code>
   */
  String Z_PARAGRAPH_LATEX_AXDEF_START = "\\begin{axdef}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>\\end{axdef}</code>
   */
  String Z_PARAGRAPH_LATEX_AXDEF_END = "\\end{axdef}"; //$NON-NLS-1$

  /* Definition for LATEX_SCHEMA */
  /**
   * The identifier of the latex Z partition content type
   * - Schema definition paragraph markup
   * @value <code>__z_paragraph_latex_schema</code>
   */
  String Z_PARAGRAPH_LATEX_SCHEMA = "__z_paragraph_latex_schema"; //$NON-NLS-1$

  /**
   * The start String of the latex Z partition content type
   * - Schema definition paragraph markup
   * @value <code>\\begin{schema}</code>
   */
  String Z_PARAGRAPH_LATEX_SCHEMA_START = "\\begin{schema}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z partition content type
   * - Schema definition paragraph markup
   * @value <code>\\end{schema}</code>
   */
  String Z_PARAGRAPH_LATEX_SCHEMA_END = "\\end{schema}"; //$NON-NLS-1$

  /* Definition for LATEX_GENAX */
  /**
   * The identifier of the latex Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>__z_paragraph_latex_genax</code>
   */
  String Z_PARAGRAPH_LATEX_GENAX = "__z_paragraph_latex_genax"; //$NON-NLS-1$

  /**
   * The start String of the latex Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>\\begin{gendef}</code>
   */
  String Z_PARAGRAPH_LATEX_GENAX_START = "\\begin{gendef}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>\\end{gendef}</code>
   */
  String Z_PARAGRAPH_LATEX_GENAX_END = "\\end{gendef}"; //$NON-NLS-1$
  
  /* Definition for LATEX_PROOFSCRIPT */
  /**
   * The identifier of the latex Z partition content type
   * - Proof script paragraph markup
   * @value <code>__z_paragraph_latex_proofscript</code>
   */
  String Z_PARAGRAPH_LATEX_PROOFSCRIPT = "__z_paragraph_latex_proofscript"; //$NON-NLS-1$

  /**
   * The start String of the latex Z partition content type
   * - Proof script paragraph markup
   * @value <code>\\begin{zproof}</code>
   */
  String Z_PARAGRAPH_LATEX_PROOFSCRIPT_START = "\\begin{zproof}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z partition content type
   * - Proof script paragraph markup
   * @value <code>\\end{zproof}</code>
   */
  String Z_PARAGRAPH_LATEX_PROOFSCRIPT_END = "\\end{zproof}"; //$NON-NLS-1$

  /* Definition for UNICODE_ZSECTION */
  /**
   * The identifier of the unicode Z partition content type
   * - Section header markup or paragraph rendered without a box
   * @value <code>__z_paragraph_unicode_zsection</code>
   */
  String Z_PARAGRAPH_UNICODE_ZSECTION = "__z_paragraph_unicode_zsection"; //$NON-NLS-1$
  String Z_PARAGRAPH_UNICODE_ZSECTION_OLD = "__z_paragraph_unicode_zsection_old"; //$NON-NLS-1$

  /**
   * The start String of the unicode Z partition content type
   * - Section header markup or paragraph rendered without a box
   * - Box drawings light horizontal
   * @value <code>\u2500</code>
   */
  String Z_PARAGRAPH_UNICODE_ZSECTION_START = ZString.ZED; //$NON-NLS-1$

  /**
   * The end String of the unicode Z partition content type
   * - Section header markup or paragraph rendered without a box
   * @value <code>\u2514</code>
   */
  String Z_PARAGRAPH_UNICODE_ZSECTION_END = ZString.END; //$NON-NLS-1$

  /* Definition for UNICODE_AXDEF */
  /**
   * The identifier of the unicode Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>__z_paragraph_unicode_axdef</code>
   */
  String Z_PARAGRAPH_UNICODE_AXDEF = "__z_paragraph_unicode_axdef"; //$NON-NLS-1$
  String Z_PARAGRAPH_UNICODE_AXDEF_OLD = "__z_paragraph_unicode_axdef_old"; //$NON-NLS-1$

  /**
   * The start String of the unicode Z partition content type
   * - Axiomatic description paragraph markup
   * - Box drawings light down
   * @value <code>\u2577</code>
   */
  String Z_PARAGRAPH_UNICODE_AXDEF_START = ZString.AX; //$NON-NLS-1$

  /**
   * The end String of the unicode Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>\u2514</code>
   */
  String Z_PARAGRAPH_UNICODE_AXDEF_END = ZString.END; //$NON-NLS-1$

  /* Definition for UNICODE_SCHEMA */
  /**
   * The identifier of the unicode Z partition content type
   * - Schema definition paragraph markup
   * @value <code>__z_paragraph_unicode_schema</code>
   */
  String Z_PARAGRAPH_UNICODE_SCHEMA = "__z_paragraph_unicode_schema"; //$NON-NLS-1$
  String Z_PARAGRAPH_UNICODE_SCHEMA_OLD = "__z_paragraph_unicode_schema_old"; //$NON-NLS-1$

  /**
   * The start String of the unicode Z partition content type
   * - Schema definition paragraph markup
   * - Box drawings light down and right
   * @value <code>\u250C</code>
   */
  String Z_PARAGRAPH_UNICODE_SCHEMA_START = ZString.SCH; //$NON-NLS-1$

  /**
   * The end String of the unicode Z partition content type
   * - Schema definition paragraph markup
   * @value <code>\u2514</code>
   */
  String Z_PARAGRAPH_UNICODE_SCHEMA_END = ZString.END; //$NON-NLS-1$

  /* Definition for UNICODE_GENAX */
  /**
   * The identifier of the unicode Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>__z_paragraph_unicode_genax</code>
   */
  String Z_PARAGRAPH_UNICODE_GENAX = "__z_paragraph_unicode_genax"; //$NON-NLS-1$
  String Z_PARAGRAPH_UNICODE_GENAX_OLD = "__z_paragraph_unicode_genax_old"; //$NON-NLS-1$

  /**
   * The start String of the unicode Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>\u2577,\u2550</code>
   */
  String Z_PARAGRAPH_UNICODE_GENAX_START = ZString.GENAX; //$NON-NLS-1$

  /**
   * The end String of the unicode Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>\u2514</code>
   */
  String Z_PARAGRAPH_UNICODE_GENAX_END = ZString.END; //$NON-NLS-1$

  /* Definition for UNICODE_GENSCH */
  /**
   * The identifier of the unicode Z partition content type
   * - Generic schema definition paragraph markup
   * @value <code>__z_paragraph_unicode_gensch</code>
   */
  String Z_PARAGRAPH_UNICODE_GENSCH = "__z_paragraph_unicode_gensch"; //$NON-NLS-1$
  String Z_PARAGRAPH_UNICODE_GENSCH_OLD = "__z_paragraph_unicode_gensch_old"; //$NON-NLS-1$

  /**
   * The start String of the unicode Z partition content type
   * - Generic schema definition paragraph markup
   * @value <code>\u250C,\u2550</code>
   */
  String Z_PARAGRAPH_UNICODE_GENSCH_START = ZString.GENSCH; //$NON-NLS-1$

  /**
   * The end String of the unicode Z partition content type
   * - Generic schema definition paragraph markup
   * @value <code>\u2514</code>
   */
  String Z_PARAGRAPH_UNICODE_GENSCH_END = ZString.END; //$NON-NLS-1$

  /**
   * The old end String of the unicode Z partition content types
   * For backward-compatibility
   * @value <code>\u2029</code>
   */
  String Z_PARAGRAPH_UNICODE_ENDCHAR_OLD = "\u2029"; //$NON-NLS-1$

  /* Definition for UNICODE_PROOFSCRIPT */
  /**
   * The identifier of the unicode Z partition content type
   * - Proof script paragraph markup
   * @value <code>__z_paragraph_unicode_schema</code>
   */
  String Z_PARAGRAPH_UNICODE_PROOFSCRIPT = "__z_paragraph_unicode_proofscript"; //$NON-NLS-1$
  String Z_PARAGRAPH_UNICODE_PROOFSCRIPT_OLD = "__z_paragraph_unicode_schema_proofscript"; //$NON-NLS-1$

  /**
   * The start String of the unicode Z partition content type
   * - Proof script paragraph markup
   * - Box drawings light down and right
   * @value <code>\u251C</code>
   */
  String Z_PARAGRAPH_UNICODE_PROOFSCRIPT_START = ZEvesString.ZPROOF; //$NON-NLS-1$

  /**
   * The end String of the unicode Z partition content type
   * - Proof script paragraph markup
   * @value <code>\u2514</code>
   */
  String Z_PARAGRAPH_UNICODE_PROOFSCRIPT_END = ZString.END; //$NON-NLS-1$

  /**
   * The start String of the latex Z conjecture paragraph
   * - ZED
   * @value <code>\\begin{theorem}</code>
   */
  String Z_PARAGRAPH_LATEX_THEOREM_START = "\\begin{theorem}"; //$NON-NLS-1$

  /**
   * The end String of the latex Z conjecture paragraph
   * - ZED
   * @value <code>\\end{theorem}</code>
   */
  String Z_PARAGRAPH_LATEX_THEOREM_END = "\\end{theorem}"; //$NON-NLS-1$

}
