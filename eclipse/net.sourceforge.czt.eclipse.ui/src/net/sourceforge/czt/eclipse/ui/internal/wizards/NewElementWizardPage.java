/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.wizards;

import net.sourceforge.czt.eclipse.ui.internal.preferences.StatusInfo;
import net.sourceforge.czt.eclipse.ui.internal.preferences.StatusUtil;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.wizard.WizardPage;

/**
 * Base class for wizard page responsible to create CZT elements. The class
 * provides API to update the wizard's status line and OK button according to
 * the value of a <code>IStatus</code> object.
 * 
 * <p>
 * Clients may subclass.
 * </p>
 * @author Chengdong Xu
 */
public abstract class NewElementWizardPage extends WizardPage
{
  private IStatus fCurrStatus;

  private boolean fPageVisible;

  /**
   * Creates a <code>NewElementWizardPage</code>.
   * 
   * @param pageName the wizard page's name
   */
  public NewElementWizardPage(String pageName)
  {
    super(pageName);
    fPageVisible = false;
    fCurrStatus = new StatusInfo();
  }

  /**
   * @param pageName the wizard page's name
   * @param title the wizard page's title
   * @param titleImage the wizard page's image descriptor
   */
  public NewElementWizardPage(String pageName, String title,
      ImageDescriptor titleImage)
  {
    super(pageName, title, titleImage);
    fPageVisible = false;
    fCurrStatus = new StatusInfo();
  }

  //---- WizardPage ----------------

  /**
   * @see org.eclipse.jface.dialogs.DialogPage#setVisible(boolean)
   */
  public void setVisible(boolean visible)
  {
    super.setVisible(visible);
    fPageVisible = visible;
    // policy: wizards are not allowed to come up with an error message
    if (visible && fCurrStatus.matches(IStatus.ERROR)) {
      StatusInfo status = new StatusInfo();
      status.setError(""); //$NON-NLS-1$
      fCurrStatus = status;
    }
    //        updateStatus(fCurrStatus);
  }

  /**
   * Updates the status line and the OK button according to the given status
   * 
   * @param status status to apply
   */
  protected void updateStatus(IStatus status)
  {
    fCurrStatus = status;
    setPageComplete(!status.matches(IStatus.ERROR));
    if (fPageVisible) {
      StatusUtil.applyToStatusLine(this, status);
    }
  }

  /**
   * Updates the status line and the OK button according to the status evaluate from
   * an array of status. The most severe error is taken.  In case that two status with 
   * the same severity exists, the status with lower index is taken.
   * 
   * @param status the array of status
   */
  protected void updateStatus(IStatus[] status)
  {
    updateStatus(StatusUtil.getMostSevere(status));
  }
}
