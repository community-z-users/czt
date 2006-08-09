/**
 * Created on 2005-10-13
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

package net.sourceforge.czt.eclipse.util;

import org.eclipse.swt.graphics.RGB;

/**
 * Color keys used for syntax highlighting z
 * code.
 * A <code>IColorManager</code> is responsible for mapping
 * concrete colors to these keys.
 * <p>
 * This interface declares static final fields only; it is not intended to be
 * implemented.
 * </p>
 *
 * @see net.sourceforge.czt.eclipse.util.IColorManager
 * 
 * @author Chengdong Xu
 */
public interface IZColorConstants
{
  public static final RGB PREDICATE = new RGB(128, 64, 0);

  public static final RGB SET = new RGB(128, 64, 0);

  public static final RGB RELATION = new RGB(128, 64, 0);

  public static final RGB FUNCTION = new RGB(128, 64, 0);

  public static final RGB SEQUENCE = new RGB(128, 64, 0);

  public static final RGB ARITHMETIC = new RGB(128, 64, 0);

  public static final RGB SCHEMA = new RGB(128, 64, 0);

  public static final RGB BACKGROUND = new RGB(64, 64, 64);

  /**
   * Note: This constant is for internal use only. Clients should not use this constant.
   * The prefix all color constants start with
   * (value <code>"czt_"</code>).
   */
  String PREFIX = "czt_"; //$NON-NLS-1$

  /**
   * The color key for narrative paragraph
   */
  String CZT_NARRATIVE_PARAGRAPH = "czt_narr_para";

  /**
   * The color key for zchar paragraph
   */
  String CZT_ZCHAR_PARAGRAPH = "czt_zchar_para";

  /**
   * The color key for section paragraph
   */
  String CZT_SECTION_PARAGRAPH = "czt_section_para";

  /**
   * The color key for zed paragraph
   */
  String CZT_ZED_PARAGRAPH = "czt_zed_para";

  /**
   * The color key for schema definition paragraph
   */
  String CZT_SCHEMA_PARAGRAPH = "czt_schema_para";

  /**
   * The color key for axiomatic description paragraph
   */
  String CZT_AX_PARAGRAPH = "czt_ax_para";

  /**
   * The color key for generic schema definition paragraph
   */
  String CZT_GEN_PARAGRAPH = "czt_gen_para";

  /** The color key for multi-line comments in Z code
   * (value <code>"czt_multi_line_comment"</code>).
   */
  String CZT_MULTI_LINE_COMMENT = "czt_multi_line_comment"; //$NON-NLS-1$

  /** The color key for single-line comments in Z code
   * (value <code>"czt_single_line_comment"</code>).
   */
  String CZT_SINGLE_LINE_COMMENT = "czt_single_line_comment"; //$NON-NLS-1$

  /** The color key for Java keywords in Z code
   * (value <code>"czt_keyword"</code>).
   */
  String CZT_KEYWORD = "czt_keyword"; //$NON-NLS-1$

  /** The color key for operators and brackets in z code
   * (value <code>"czt_operator"</code>).
   */
  String CZT_OPERATOR = "czt_operator"; //$NON-NLS-1$

  /**
   * The color key for everything in Java code for which no other color is specified
   * (value <code>"czt_default"</code>).
   */
  String CZT_DEFAULT = "czt_default"; //$NON-NLS-1$

}
