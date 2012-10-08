/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import org.eclipse.jface.text.formatter.FormattingContext;

/**
 * Formatting context for Z
 * 
 * @author Chengdong Xu
 */
public class ZFormattingContext extends FormattingContext
{

  /**
   * 
   */
  public ZFormattingContext()
  {
    super();
  }

  /**
   * @see org.eclipse.jface.text.formatter.IFormattingContext#getPreferenceKeys()
   */
  public String[] getPreferenceKeys()
  {
    return super.getPreferenceKeys();
  }

  /*
   * @see org.eclipse.jface.text.formatter.IFormattingContext#isBooleanPreference(java.lang.String)
   */
  public boolean isBooleanPreference(String key)
  {
    return super.isBooleanPreference(key);
  }

  /*
   * @see org.eclipse.jface.text.formatter.IFormattingContext#isIntegerPreference(java.lang.String)
   */
  public boolean isIntegerPreference(String key)
  {
    return super.isIntegerPreference(key);
  }

}
