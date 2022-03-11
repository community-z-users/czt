/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.util;

import org.eclipse.jface.text.source.ISharedTextColors;
import org.eclipse.swt.graphics.Color;

/**
 * Manages SWT color objects for the given color keys and
 * given <code>RGB</code> objects. Until the <code>dispose</code>
 * method is called, the same color object is returned for
 * equal keys and equal <code>RGB</code> values.
 * <p>
 * In order to provide backward compatibility for clients of <code>IColorManager</code>, extension
 * interfaces are used to provide a means of evolution. The following extension interfaces exist:
 * <ul>
 * <li>{@link org.eclipse.jdt.ui.text.IColorManagerExtension} since version 2.0 introducing
 * 		the ability to bind and un-bind colors.</li>
 * </ul>
 * </p>
 * <p>
 * This interface may be implemented by clients.
 * </p>
 *
 * @see org.eclipse.jdt.ui.text.IColorManagerExtension
 * @see org.eclipse.jdt.ui.text.IJavaColorConstants
 * 
 * @author Chengdong Xu
 */
public interface IZColorManager extends ISharedTextColors
{
  /**
   * Returns a color object for the given key. The color objects
   * are remembered internally; the same color object is returned
   * for equal keys.
   *
   * @param key the color key
   * @return the color object for the given key
   */
  Color getColor(String key);
}
