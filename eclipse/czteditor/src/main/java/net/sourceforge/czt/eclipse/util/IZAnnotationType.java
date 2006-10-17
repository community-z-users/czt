/**
 * 
 */

package net.sourceforge.czt.eclipse.util;

/**
 * The types of CZT annotations
 * 
 * @author Chengdong Xu
 */
public interface IZAnnotationType
{

  /**
   * CZT error annotation type
   * to be used to present an error
   */
  public final String ERROR = "net.sourceforge.czt.eclipse.error";

  /**
   * CZT warning annotation type
   * to be used to present a warning
   */
  public final String WARNING = "net.sourceforge.czt.eclipse.warning";

  /**
   * CZT info annotation type
   * to be used to present some information
   */
  public final String INFO = "net.sourceforge.czt.eclipse.info";

  /**
   * CZT task annotation type
   * to be used to present a task
   */
  public final String TASK = "net.sourceforge.czt.eclipse.task";

  /**
   * CZT bookmark annotation type
   * to be used to present a bookmark
   */
  public final String BOOKMARK = "net.sourceforge.czt.eclipse.bookmark";

  /**
   * CZT occurrence annotation type,
   * to be used to present an occurrence of (a referrence to) a term
   */
  public final String OCCURRENCE = "net.sourceforge.czt.eclipse.occurrence";

  /**
   * CZT term highlight annotation type
   */
  public final String TERMHIGHLIGHT = "net.sourceforge.czt.eclipse.termhighlight";
  
  /**
   * CZT schema box annotation type
   */
  public final String SCHEMABOX = "net.sourceforge.czt.eclipse.schemabox";
}
