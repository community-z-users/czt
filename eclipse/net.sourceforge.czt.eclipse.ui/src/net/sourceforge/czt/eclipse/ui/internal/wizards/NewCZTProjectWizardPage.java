/**
 *
 */

package net.sourceforge.czt.eclipse.ui.internal.wizards;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;

/**
 * @author Chengdong Xu
 */
public class NewCZTProjectWizardPage extends WizardNewProjectCreationPage
{

  private String fWorkspacePath;

  private IProject fProject;

  /**
   * @param pageName
   */
  public NewCZTProjectWizardPage(String pageName)
  {
    super(pageName);
  }

  /**
   * @see org.eclipse.ui.dialogs.WizardNewProjectCreationPage#createControl(org.eclipse.swt.widgets.Composite)
   */
  public void createControl(Composite parent)
  {
    super.createControl(parent);
    fWorkspacePath = ResourcesPlugin.getWorkspace().getRoot().getLocation()
        .addTrailingSeparator().toOSString();
  }
  
  protected String getWorkspacePath()
  {
	  return fWorkspacePath;
  }

  public void performFinish(IProgressMonitor monitor)
  {
    if (monitor == null)
      monitor = new NullProgressMonitor();
    try {
      monitor.beginTask(WizardsMessages.NewCZTProjectWizardPage_progressCreating, 12);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      String name = getProjectName();
      IProject project = root.getProject(name);
      monitor.worked(1);

      createProject(project, monitor);
      monitor.worked(1);
      addProjectNature(project, monitor);
      monitor.worked(1);
      monitor.worked(1);
      monitor.worked(1);
      monitor.worked(1);
      monitor.worked(1);
      monitor.worked(1);

    } catch (CoreException e) {
      //          CZTPlugin.log("projectWizardCreateError", e);
      e.printStackTrace();
    } finally {
      monitor.done();
    }
  }

  /**
   * Create the project directory.
   * If the user has specified an external project location,
   * the project is created with a custom description for the location.
   *
   * @param project project
   * @param monitor progress monitor
   * @throws CoreException
   */
  private void createProject(IProject project, IProgressMonitor monitor)
      throws CoreException
  {

    monitor.subTask(WizardsMessages.NewCZTProjectWizardPage_progressDirectory);

    if (!project.exists()) {

      IPath projectPath = getLocationPath().addTrailingSeparator().append(
          getProjectName());
      if (!ResourcesPlugin.getWorkspace().getRoot().getLocation().equals(
          getLocationPath())) {
        IProjectDescription desc = project.getWorkspace()
            .newProjectDescription(project.getName());
        IStatus status = ResourcesPlugin.getWorkspace()
            .validateProjectLocation(project, projectPath);
        if (status.getSeverity() != IStatus.OK) {
          throw new CoreException(status);
        }
        desc.setLocation(projectPath);
        project.create(desc, monitor);
      }
      else {
        project.create(monitor);
      }
    }
    if (!project.isOpen()) {
      project.open(monitor);
    }

    fProject = project;
  }

  /**
   * Add a nature to the project.
   *
   * @param project project
   * @param monitor progress monitor
   * @throws CoreException
   */
  public static void addProjectNature(IProject project, IProgressMonitor monitor)
      throws CoreException
  {
    /*
     monitor.subTask("projectWizardProgressNature");

     IProjectDescription desc = project.getDescription();
     String[] natures = desc.getNatureIds();
     for (int i = 0; i < natures.length; i++) {
     // don't add if already there
     if (CZTNature.NATURE_ID.equals(natures[i])) {
     return;
     }
     }

     String[] newNatures = new String[natures.length + 1];
     System.arraycopy(natures, 0, newNatures, 1, natures.length);
     newNatures[0] = TexlipseNature.NATURE_ID;
     desc.setNatureIds(newNatures);
     project.setDescription(desc, monitor);
     */
  }

  protected IProject getProject()
  {
    return fProject;
  }
}
