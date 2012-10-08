/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.editors.text.EditorsUI;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class CZTPreferenceInitializer extends AbstractPreferenceInitializer
{

  /**
   * 
   */
  public CZTPreferenceInitializer()
  {
    super();
  }

  /**
   * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
   */
  @Override
  public void initializeDefaultPreferences()
  {
    IPreferenceStore store = PreferenceConstants.getPreferenceStore();
    EditorsUI.useAnnotationsPreferencePage(store);
    EditorsUI.useQuickDiffPreferencePage(store);
    PreferenceConstants.initializeDefaultValues(store);
  }
}
