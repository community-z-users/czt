/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.util;


import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.core.resources.IMarker;

/**
 * @author Chengdong Xu
 */
public interface IZMarker extends IMarker
{

  /**
   * CZT problem marker type
   */
  public final String PROBLEM = CztUIPlugin.PLUGIN_ID + ".problemmarker";

  /**
   * CZT task marker type
   */
  public final String TASK = CztUIPlugin.PLUGIN_ID + ".taskmarker";

  /**
   * CZT bookmark marker type
   */
  public final String BOOKMARK = CztUIPlugin.PLUGIN_ID + ".bookmarkmarker";

  /**
   * CZT occurrence marker type
   */
  public final String OCCURRENCE = CztUIPlugin.PLUGIN_ID + ".occurrencemarker";

  /**
   * CZT term highlight marker type
   */
  public final String TERMHIGHLIGHT = CztUIPlugin.PLUGIN_ID + ".termhighlightmarker";

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
