/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.PlatformUI;

/**
 * Abstract preference page which is used to wrap a
 * {@link net.sourceforge.eclipse.czt.preferences.IPreferenceConfigurationBlock}.
 * 
 * @author Chengdong Xu
 */
public abstract class AbstractConfigurationBlockPreferencePage
    extends
      PreferencePage implements IWorkbenchPreferencePage
{

  private IPreferenceConfigurationBlock fConfigurationBlock;

  private OverlayPreferenceStore fOverlayStore;

  /**
   * Creates a new preference page.
   */
  public AbstractConfigurationBlockPreferencePage()
  {
    setDescription();
    setPreferenceStore();
    fOverlayStore = new OverlayPreferenceStore(getPreferenceStore(),
        new OverlayPreferenceStore.OverlayKey[]{});
    fConfigurationBlock = createConfigurationBlock(fOverlayStore);
  }

  protected abstract IPreferenceConfigurationBlock createConfigurationBlock(
      OverlayPreferenceStore overlayPreferenceStore);

  protected abstract String getHelpId();

  protected abstract void setDescription();

  protected abstract void setPreferenceStore();

  /**
   * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
   */
  public void init(IWorkbench workbench)
  {
  }

  /**
   * @see org.eclipse.jface.preference.PreferencePage#createControl(Composite)
   */
  public void createControl(Composite parent)
  {
    super.createControl(parent);
    PlatformUI.getWorkbench().getHelpSystem()
        .setHelp(getControl(), getHelpId());
  }

  /**
   * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
   */
  protected Control createContents(Composite parent)
  {
    fOverlayStore.load();
    fOverlayStore.start();

    Control content = fConfigurationBlock.createControl(parent);

    initialize();

    Dialog.applyDialogFont(content);
    return content;
  }

  private void initialize()
  {
    fConfigurationBlock.initialize();
  }

  /**
   * @see org.eclipse.jface.preference.PreferencePage#performOk()
   */
@SuppressWarnings("deprecation")
// TODO: deprecation!
public boolean performOk()
  {

    fConfigurationBlock.performOk();

    fOverlayStore.propagate();

    CztUIPlugin.getDefault().savePluginPreferences();

    return true;
  }

  /**
   * @see org.eclipse.jface.preference.PreferencePage#performDefaults()
   */
  public void performDefaults()
  {

    fOverlayStore.loadDefaults();
    fConfigurationBlock.performDefaults();

    super.performDefaults();
  }

  /*
   * @see DialogPage#dispose()
   */
  public void dispose()
  {

    fConfigurationBlock.dispose();

    if (fOverlayStore != null) {
      fOverlayStore.stop();
      fOverlayStore = null;
    }

    super.dispose();
  }
}
