/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.util;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

/**
 * The types of CZT annotations
 * 
 * @author Chengdong Xu
 */
public interface IZAnnotationType
{

  static final String ANN_ID = CztUIPlugin.PLUGIN_ID + ".annotation";
  
  /**
   * CZT error annotation type
   * to be used to present an error
   */
  public final String ERROR = ANN_ID + ".error";

  /**
   * CZT warning annotation type
   * to be used to present a warning
   */
  public final String WARNING = ANN_ID + ".warning";

  /**
   * CZT info annotation type
   * to be used to present some information
   */
  public final String INFO = ANN_ID + ".info";

  /**
   * CZT task annotation type
   * to be used to present a task
   */
  public final String TASK = ANN_ID + ".task";

  /**
   * CZT bookmark annotation type
   * to be used to present a bookmark
   */
  public final String BOOKMARK = ANN_ID + ".bookmark";

  /**
   * CZT occurrence annotation type,
   * to be used to present an occurrence of (a referrence to) a term
   */
  public final String OCCURRENCE = ANN_ID + ".occurrence";

  /**
   * CZT term highlight annotation type
   */
  public final String TERMHIGHLIGHT = ANN_ID + ".termhighlight";
  
  /**
   * CZT schema box annotation type
   */
  public final String SCHEMABOX = ANN_ID + ".schemabox";
}
