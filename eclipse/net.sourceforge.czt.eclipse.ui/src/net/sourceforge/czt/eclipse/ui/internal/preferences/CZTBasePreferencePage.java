/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author Chengdong Xu
 *
 */
public class CZTBasePreferencePage extends PreferencePage
    implements
      IWorkbenchPreferencePage
{

  /**
   * 
   */
  public CZTBasePreferencePage()
  {
    super();
    setPreferenceStore(CztUIPlugin.getDefault().getPreferenceStore());
    setDescription(PreferencesMessages.CZTBasePreferencePage_description);
  }
  
  /* (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
   */
  public void init(IWorkbench workbench)
  {
  }
  
  /*
   * @see org.eclipse.jface.preference.PreferencePage#createControl(org.eclipse.swt.widgets.Composite)
   */
  public void createControl(Composite parent)
  {
    super.createControl(parent);
//    PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), IJavaHelpContextIds.JAVA_BASE_PREFERENCE_PAGE);
  }
  
  /* (non-Javadoc)
   * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
   */
  @Override
  protected Control createContents(Composite parent)
  {
    initializeDialogUnits(parent);

    Composite result = new Composite(parent, SWT.NONE);
    
    Dialog.applyDialogFont(result);
    return result;
  }
}
