/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.wizards;

import java.lang.reflect.InvocationTargetException;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.util.ExceptionHandler;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.IWizard;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbench;

/**
 * This is a Z specification new wizard. Its role is to create a new file 
 * resource in the provided container. If the container resource
 * (a folder or a project) is selected in the workspace 
 * when the wizard is opened, it will accept it as the target
 * container. The wizard creates one file with one of the following extensions
 * "tex", "utf8", "utf16".
 * 
 * @author Chengdong Xu
 */
public class NewZSpecificationWizard extends NewElementWizard
{

  private NewZSpecificationWizardPage fMainPage;

  /**
   * 
   */
  public NewZSpecificationWizard()
  {
    super();
    setDefaultPageImageDescriptor(null);
    setDialogSettings(CztUIPlugin.getDefault().getDialogSettings());
  }

  /**
   * Adding the page to the wizard.
   */

  public void addPages()
  {
    fMainPage = new NewZSpecificationWizardPage(getSelection());
    fMainPage.setTitle(WizardsMessages.NewZSpecificationWizard_title);
    fMainPage.setDescription(WizardsMessages.NewZSpecificationWizard_description);
    addPage(fMainPage);
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.internal.wizards.NewElementWizard#finishPage(org.eclipse.core.runtime.IProgressMonitor)
   */
  @Override
  protected void finishPage(IProgressMonitor monitor)
      throws InterruptedException, CoreException
  {
    fMainPage.performFinish(monitor); // use the full progress monitor
  }

  /**
   * Finish the project creation, i.e. run the ProjectCreationOperation.
   * @return false on error
   * @see org.eclipse.jface.wizard.Wizard#performFinish()
   */
  @Override
  public boolean performFinish()
  {
    boolean result = super.performFinish();

    if (result) {
      selectAndReveal(fMainPage.getFile());
      openResource(fMainPage.getFile());
    }

    return result;
  }

  protected void handleFinishException(Shell shell, InvocationTargetException e)
  {
    String title = WizardsMessages.NewZSpecificationWizard_exception_title;
    String message = WizardsMessages.NewZSpecificationWizard_exception_message;
    ExceptionHandler.handle(e, getShell(), title, message);
  }

  /**
   * Useful method for e.g. loading images for the wizard.
   * 
   * @param workbench
   * @param selection
   * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench, org.eclipse.jface.viewers.IStructuredSelection)
   */
  public void init(IWorkbench workbench, IStructuredSelection selection)
  {
    super.init(workbench, selection);
    setWindowTitle(WizardsMessages.NewZSpecificationWizard_windowtitle);
    setNeedsProgressMonitor(true);
  }

  /**
   * @see IWizard#performCancel()
   */
  public boolean performCancel()
  {
    //      fMainPage.performCancel();
    return super.performCancel();
  }

}
