/**
 * 
 */

package net.sourceforge.czt.eclipse.wizards;

import java.lang.reflect.InvocationTargetException;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.util.ExceptionHandler;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExecutableExtension;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.dialogs.WizardNewProjectReferencePage;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

/**
 * A basic CZT project creation wizard.
 * 
 * @author Chengdong Xu
 */
public class NewCZTProjectWizard extends NewElementWizard
    implements
      IExecutableExtension
{

  NewCZTProjectWizardPage fMainPage;

  // the perspective configuration element 
  private IConfigurationElement fConfigElement;

  /**
   * Create new wizard
   */
  public NewCZTProjectWizard()
  {
    super();
    setDefaultPageImageDescriptor(null);
    setDialogSettings(CZTPlugin.getDefault().getDialogSettings());
  }

  /**
   * Add pages to the wizard.
   * @see org.eclipse.jface.wizard.Wizard#addPages()
   */
  public void addPages()
  {
    super.addPages();
    //      fMainPage = new SampleProjectWizardPage("BasicNewProjectCreationPage");
    fMainPage = new NewCZTProjectWizardPage("BasicNewProjectCreationPage");
    fMainPage.setTitle("Project");
    fMainPage.setDescription("Creat a new CZT project");
    addPage(fMainPage);
  }

  /**
   * @see org.eclipse.jdt.internal.ui.wizards.NewElementWizard#finishPage(org.eclipse.core.runtime.IProgressMonitor)
   */
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
      BasicNewProjectResourceWizard.updatePerspective(fConfigElement);
      selectAndReveal(fMainPage.getProject());
    }

    return result;
  }

  protected void handleFinishException(Shell shell, InvocationTargetException e)
  {
    String title = "NewWizardMessages.CZTProjectWizard_op_error_title";
    String message = "NewWizardMessages.CZTProjectWizard_op_error_create_message";
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
    setWindowTitle("Customized Wizard Title");
    setNeedsProgressMonitor(true);
  }

  /**
   * Useful method for e.g. getting config element info.
   * 
   * @param config
   * @param propertyName
   * @param data
   * @see org.eclipse.core.runtime.IExecutableExtension#setInitializationData(org.eclipse.core.runtime.IConfigurationElement, java.lang.String, java.lang.Object)
   */
  public void setInitializationData(IConfigurationElement config,
      String propertyName, Object data) throws CoreException
  {
    fConfigElement = config;
  }

  /* (non-Javadoc)
   * @see IWizard#performCancel()
   */
  public boolean performCancel()
  {
    //      fMainPage.performCancel();
    return super.performCancel();
  }
}
