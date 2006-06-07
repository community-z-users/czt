/**
 * 
 */

package net.sourceforge.czt.eclipse.editors;

/**
 * /**
 * Definition of Z partitioning and its partitions.
 *
 * @since 3.1
 * 
 * @author Chengdong Xu
 */
public interface IZPartitions
{

  /**
   * The identifier of the Java partitioning.
   */
  String Z_PARTITIONING = "___zed_partitioning"; //$NON-NLS-1$

  /**
   * The identifier of the zchar latex partition content type
   */
  String Z_PARAGRAPH_LATEX_ZCHAR = "__z_paragraph_latex_zchar"; //$NON-NLS-1$

  /**
   * The identifier of the section latex partition content type
   */
  String Z_PARAGRAPH_LATEX_ZSECTION = "__z_paragraph_latex_zsection"; //$NON-NLS-1$

  /**
   * The identifier of the zed latex partition content type
   */
  String Z_PARAGRAPH_LATEX_ZED = "__z_paragraph_latex_zed"; //$NON-NLS-1$

  /**
   * The identifier of the sechma latex partition content type
   */
  String Z_PARAGRAPH_LATEX_SCHEMA = "__z_paragraph_latex_schema"; //$NON-NLS-1$

  /**
   * The identifier of the ax latex partition content type
   */
  String Z_PARAGRAPH_LATEX_AXDEF = "__z_paragraph_latex_axdef"; //$NON-NLS-1$

  /**
   * The identifier of the gen latex partition content type
   */
  String Z_PARAGRAPH_LATEX_GENDEF = "__z_paragraph_latex_gendef"; //$NON-NLS-1$

  /**
   * The identifier of the section unicode partition content type
   */
  String Z_PARAGRAPH_UNICODE_ZSECTION = "__z_paragraph_latex_zsection"; //$NON-NLS-1$

  /**
   * The identifier of the zed unicode partition content type
   */
  String Z_PARAGRAPH_UNICODE_ZED = "__z_paragraph_unicode_zed"; //$NON-NLS-1$

  /**
   * The identifier of the schema unicode partition content type
   */
  String Z_PARAGRAPH_UNICODE_SCHEMA = "__z_paragraph_unicode_schema"; //$NON-NLS-1$

  /**
   * The identifier of the ax unicode partition content type
   */
  String Z_PARAGRAPH_UNICODE_AXDEF = "__z_paragraph_unicode_axdef"; //$NON-NLS-1$

  /**
   * The identifier of the gen unicode partition content type
   */
  String Z_PARAGRAPH_UNICODE_GENDEF = "__z_paragraph_unicode_gendef"; //$NON-NLS-1$
}
