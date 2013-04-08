package net.sourceforge.czt.eclipse.ui.internal.wizards;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExecutableExtension;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;

import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.actions.WorkspaceModifyOperation;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;


/**
 * @author Andrius Velykis
 */
// adapted from org.eclipse.jdt.ui.examples.MyProjectCreationWizard
public class NewCZTProjectWizard extends Wizard implements IExecutableExtension, INewWizard {

  private WizardNewProjectCreationPage fMainPage;

  private IConfigurationElement fConfigElement;

  private IWorkbench fWorkbench;
  public NewCZTProjectWizard() {
    setWindowTitle(WizardsMessages.NewCZTProjectWizard_initWindowTitle);
  }

  /* (non-Javadoc)
   * @see org.eclipse.core.runtime.IExecutableExtension#setInitializationData(org.eclipse.core.runtime.IConfigurationElement, java.lang.String, java.lang.Object)
   */
  public void setInitializationData(IConfigurationElement cfig, String propertyName, Object data) {
    //  The config element will be used in <code>finishPage</code> to set the result perspective.
    fConfigElement= cfig;
  }

  /* (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench, org.eclipse.jface.viewers.IStructuredSelection)
   */
  public void init(IWorkbench workbench, IStructuredSelection selection) {
    fWorkbench= workbench;
  }

  /* (non-Javadoc)
   * @see Wizard#addPages
   */
  public void addPages() {
    super.addPages();
    fMainPage= new WizardNewProjectCreationPage("NewCZTProjectCreationWizard"); //$NON-NLS-1$
    fMainPage.setTitle(WizardsMessages.NewCZTProjectWizard_page_title);
    fMainPage.setDescription(WizardsMessages.NewCZTProjectWizard_page_description);

    // the main page
    addPage(fMainPage);
  }

  private void updatePage() {
  }

  private void finishPage(IProgressMonitor monitor) throws InterruptedException, CoreException {
    if (monitor == null) {
      monitor= new NullProgressMonitor();
    }
    try {
      monitor.beginTask(WizardsMessages.NewCZTProjectWizardPage_progressCreating, 3); // 3 steps

      IProject project= fMainPage.getProjectHandle();
      IPath locationPath= fMainPage.getLocationPath();

      // create the project
      IProjectDescription desc= project.getWorkspace().newProjectDescription(project.getName());
      if (!fMainPage.useDefaults()) {
        desc.setLocation(locationPath);
      }
      project.create(desc, new SubProgressMonitor(monitor, 1));
      project.open(new SubProgressMonitor(monitor, 1));

      updatePage();

      // TODO: configure CZT project / nature
      monitor.worked(1);

      // change to the perspective specified in the plugin.xml
      BasicNewProjectResourceWizard.updatePerspective(fConfigElement);
      BasicNewResourceWizard.selectAndReveal(project, fWorkbench.getActiveWorkbenchWindow());

    } finally {
      monitor.done();
    }
  }

  /* (non-Javadoc)
   * @see Wizard#performFinish
   */
  public boolean performFinish() {
    WorkspaceModifyOperation op= new WorkspaceModifyOperation() {
      protected void execute(IProgressMonitor monitor) throws CoreException,
          InvocationTargetException, InterruptedException {
        finishPage(monitor);
      }
    };
    try {
      getContainer().run(false, true, op);
    } catch (InvocationTargetException e) {
      return false; // TODO: should open error dialog and log
    } catch  (InterruptedException e) {
      return false; // canceled
    }
    return true;
  }



}