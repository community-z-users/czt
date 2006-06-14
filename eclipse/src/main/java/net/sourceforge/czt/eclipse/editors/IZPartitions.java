/**
 * 
 */

package net.sourceforge.czt.eclipse.editors;

/**
 * /**
 * Definition of Z partitioning and its partitions.
 * 
 * @author Chengdong Xu
 */
public interface IZPartitions
{

  /**
   * The identifier of the Z partitioning.
   */
  String Z_PARTITIONING = "___z_partitioning"; //$NON-NLS-1$

  /**
   * The identifier of the zchar latex partition content type
   * - ZCHAR
   * @value <code>__z_paragraph_latex_zchar</code>
   */
  String Z_PARAGRAPH_LATEX_ZCHAR = "__z_paragraph_latex_zchar"; //$NON-NLS-1$
  
  /**
   * The identifier of the latex Z partition content type
   * - ZED
   * @value <code>__z_paragraph_latex_zed</code>
   */
  String Z_PARAGRAPH_LATEX_ZED = "__z_paragraph_latex_zed"; //$NON-NLS-1$

  /**
   * The identifier of the latex Z partition content type
   * - Section header markup
   * @value <code>__z_paragraph_latex_zsection</code>
   */
  String Z_PARAGRAPH_LATEX_ZSECTION = "__z_paragraph_latex_zsection"; //$NON-NLS-1$
  
  /**
   * The identifier of the latex Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>__z_paragraph_latex_axdef</code>
   */
  String Z_PARAGRAPH_LATEX_AXDEF = "__z_paragraph_latex_axdef"; //$NON-NLS-1$

  /**
   * The identifier of the latex Z partition content type
   * - Schema definition paragraph markup
   * @value <code>__z_paragraph_latex_schema</code>
   */
  String Z_PARAGRAPH_LATEX_SCHEMA = "__z_paragraph_latex_schema"; //$NON-NLS-1$

  /**
   * The identifier of the latex Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>__z_paragraph_latex_genax</code>
   */
  String Z_PARAGRAPH_LATEX_GENAX = "__z_paragraph_latex_genax"; //$NON-NLS-1$
  
  /**
   * The identifier of the latex Z partition content type
   * - Generic schema definition paragraph markup
   * @value <code>__z_paragraph_latex_gensch</code>
   */
  String Z_PARAGRAPH_LATEX_GENSCH = "__z_paragraph_latex_gensch"; //$NON-NLS-1$

  /**
   * The identifier of the unicode Z partition content type
   * - Section header markup or paragraph rendered without a box
   * @value <code>__z_paragraph_unicode_zsection</code>
   */
  String Z_PARAGRAPH_UNICODE_ZSECTION = "__z_paragraph_unicode_zsection"; //$NON-NLS-1$
  
  /**
   * The identifier of the unicode Z partition content type
   * - Axiomatic description paragraph markup
   * @value <code>__z_paragraph_unicode_axdef</code>
   */
  String Z_PARAGRAPH_UNICODE_AXDEF = "__z_paragraph_unicode_axdef"; //$NON-NLS-1$
  
  /**
   * The identifier of the unicode Z partition content type
   * - Schema definition paragraph markup
   * @value <code>__z_paragraph_unicode_schema</code>
   */
  String Z_PARAGRAPH_UNICODE_SCHEMA = "__z_paragraph_unicode_schema"; //$NON-NLS-1$
  
  /**
   * The identifier of the unicode Z partition content type
   * - Generic axiomatic description paragraph markup
   * @value <code>__z_paragraph_unicode_genax</code>
   */
  String Z_PARAGRAPH_UNICODE_GENAX = "__z_paragraph_unicode_genax"; //$NON-NLS-1$
  
  /**
   * The identifier of the unicode Z partition content type
   * - Generic schema definition paragraph markup
   * @value <code>__z_paragraph_unicode_gensch</code>
   */
  String Z_PARAGRAPH_UNICODE_GENSCH = "__z_paragraph_unicode_gensch"; //$NON-NLS-1$
}
