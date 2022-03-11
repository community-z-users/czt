/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

/**
 * @author Chengdong Xu
 *
 */
public class ZEditorAnnotationPreferencePage extends AbstractConfigurationBlockPreferencePage
{

  /*
   * @see org.eclipse.ui.internal.editors.text.AbstractConfigureationBlockPreferencePage#getHelpId()
   */
  protected String getHelpId()
  {
//    return IJavaHelpContextIds.JAVA_EDITOR_PREFERENCE_PAGE;
    return null;
  }

  /*
   * @see org.eclipse.ui.internal.editors.text.AbstractConfigurationBlockPreferencePage#setDescription()
   */
  protected void setDescription()
  {
    String description = PreferencesMessages.ZEditorPreferencePage_annotation_description;
    setDescription(description);
  }

  /*
   * @see org.org.eclipse.ui.internal.editors.text.AbstractConfigurationBlockPreferencePage#setPreferenceStore()
   */
  protected void setPreferenceStore()
  {
    setPreferenceStore(CztUIPlugin.getDefault().getPreferenceStore());
  }

  protected Label createDescriptionLabel(Composite parent)
  {
    return null; // no description for new look.
  }

  /*
   * @see org.eclipse.ui.internal.editors.text.AbstractConfigureationBlockPreferencePage#createConfigurationBlock(org.eclipse.ui.internal.editors.text.OverlayPreferenceStore)
   */
  protected IPreferenceConfigurationBlock createConfigurationBlock(
      OverlayPreferenceStore overlayPreferenceStore)
  {
    return new ZEditorAnnotationConfigurationBlock(this, overlayPreferenceStore);
  }
}
