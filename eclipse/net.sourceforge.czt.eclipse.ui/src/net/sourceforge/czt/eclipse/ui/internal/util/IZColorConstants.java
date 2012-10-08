/**
 * Created on 2005-10-13
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

package net.sourceforge.czt.eclipse.ui.internal.util;

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
 * @see net.sourceforge.czt.eclipse.ui.internal.util.IColorManager
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
  
  /** The color key for comments in Z code
   * (value <code>"czt_comment"</code>).
   */
  String CZT_COMMENT = "czt_comment"; //$NON-NLS-1$
  
  /**
   * The color key for narrative section or paragraph
   * (value <code>"czt_narrative"</code>).
   */
  String CZT_NARRATIVE = "czt_narrative";
}
