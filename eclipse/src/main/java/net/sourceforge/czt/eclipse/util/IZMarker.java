/**
 * 
 */
package net.sourceforge.czt.eclipse.util;

import org.eclipse.core.resources.IMarker;

/**
 * @author Chengdong Xu
 */
public interface IZMarker extends IMarker {
	/**
	 * CZT problem marker type
	 */
	public final String PROBLEM = "net.sourceforge.czt.eclipse.problemmarker";
	/**
	 * CZT task marker type
	 */
	public final String TASK = "net.sourceforge.czt.eclipse.taskmarker";
	/**
	 * CZT bookmark marker type
	 */
	public final String BOOKMARK = "net.sourceforge.czt.eclipse.bookmarkmarker";
	/**
	 * CZT occurrence marker type
	 */
	public final String OCCURRENCE = "net.sourceforge.czt.eclipse.occurrencemarker";
	/**
	 * CZT marker attribute
	 */
	public final String ID = "id";
	/**
	 * CZT marker attribute, currently used for occurrences
	 */
	public final String TERM = "term";
}
