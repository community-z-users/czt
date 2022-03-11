/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.util;

import org.eclipse.jface.text.source.ISharedTextColors;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * Manages SWT color objects for the given color keys and
 * given <code>RGB</code> objects. Until the <code>dispose</code>
 * method is called, the same color object is returned for
 * equal keys and equal <code>RGB</code> values.
 * <p>
 * This interface may be implemented by clients.
 * </p>
 *
 * @see net.sourceforge.czt.eclipse.ui.internal.util.IZColorConstants
 * 
 * @author Chengdong Xu
 */
public interface IColorManager extends ISharedTextColors
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

  /**
   * Returns a color object for the given RGB value. The color objects
   * are remembered internally; the same color object is returned
   * for equal rgbs.
   */
  //    Color getColor(RGB rgb);
  /**
   * Remembers the given color specification under the given key.
   *
   * @param key the color key
   * @param rgb the color specification
   * @throws java.lang.UnsupportedOperationException if there is already a
   *  color specification remembered under the given key
   */
  void bindColor(String key, RGB rgb);

  /**
   * Forgets the color specification remembered under the given key.
   *
   * @param key the color key
   */
  void unbindColor(String key);
}
