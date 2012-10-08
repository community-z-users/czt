/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

/**
 * Syntax coloring preference page.
 * <p>
 * Note: Must be public since it is referenced from plugin.xml
 * </p>
 * 
 * @since 1.0
 * 
 * @author Chengdong Xu
 */
public class ZEditorSyntaxColoringPreferencePage
    extends
      AbstractConfigurationBlockPreferencePage
{

  /**
   * @see org.eclipse.ui.internal.editors.text.AbstractConfigureationBlockPreferencePage#getHelpId()
   */
  protected String getHelpId()
  {
    return null;
  }

  /**
   * @see org.eclipse.ui.internal.editors.text.AbstractConfigurationBlockPreferencePage#setDescription()
   */
  protected void setDescription()
  {
    String description = PreferencesMessages.ZEditorPreferencePage_colors;
    setDescription(description);
  }

  protected Label createDescriptionLabel(Composite parent)
  {
    return null;
  }

  /**
   * @see org.org.eclipse.ui.internal.editors.text.AbstractConfigurationBlockPreferencePage#setPreferenceStore()
   */
  protected void setPreferenceStore()
  {
    setPreferenceStore(CztUIPlugin.getDefault().getPreferenceStore());
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.preferences.AbstractConfigureationBlockPreferencePage#createConfigurationBlock(org.eclipse.ui.internal.editors.text.OverlayPreferenceStore)
   */
  protected IPreferenceConfigurationBlock createConfigurationBlock(
      OverlayPreferenceStore overlayPreferenceStore)
  {
    return new ZEditorSyntaxColoringConfigurationBlock(overlayPreferenceStore);
  }
}
