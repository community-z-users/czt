/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.util;


import org.eclipse.core.resources.IMarker;

/**
 * @author Chengdong Xu
 */
public interface IZMarker extends IMarker
{

  /**
   * CZT problem marker type
   */
  public final String PROBLEM = CztUI.ID_PLUGIN + ".ui.problemmarker";

  /**
   * CZT task marker type
   */
  public final String TASK = CztUI.ID_PLUGIN + ".ui.taskmarker";

  /**
   * CZT bookmark marker type
   */
  public final String BOOKMARK = CztUI.ID_PLUGIN + ".ui.bookmarkmarker";

  /**
   * CZT occurrence marker type
   */
  public final String OCCURRENCE = CztUI.ID_PLUGIN + ".ui.occurrencemarker";

  /**
   * CZT term highlight marker type
   */
  public final String TERMHIGHLIGHT = CztUI.ID_PLUGIN
      + ".ui.termhighlightmarker";

  /**
   * CZT marker attribute,
   * to be used to store the ID responding to the problem (error/warning/info)
   * and thus be used for generating the information of resolutions
   */
  public final String PROBLEMID = "problemId";

  /**
   * CZT marker attribute,
   * to be used to store the ID responding to the task
   */
  public final String TASKID = "taskId";

  /**
   * CZT marker attribute,
   * to be used to store the ID responding to the bookmark
   */
  public final String BOOKMARKID = "bookmarkId";

  /**
   * CZT marker attribute,
   * to be used to store the term (maybe the type) underlying the highlighted texts
   */
  public final String TERM = "term";
}
