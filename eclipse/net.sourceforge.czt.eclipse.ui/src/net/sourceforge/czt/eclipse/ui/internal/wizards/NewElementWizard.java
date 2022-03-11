/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.wizards;

import java.lang.reflect.InvocationTargetException;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.util.ExceptionHandler;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.actions.WorkspaceModifyDelegatingOperation;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

/**
 * @author Chengdong Xu
 */
public abstract class NewElementWizard extends Wizard implements INewWizard
{

  private IWorkbench fWorkbench;

  private IStructuredSelection fSelection;

  /**
   * 
   */
  public NewElementWizard()
  {
    setNeedsProgressMonitor(true);
  }

  protected void openResource(final IFile resource)
  {
    final IWorkbenchPage activePage = CztUIPlugin.getActivePage();
    if (activePage != null) {
      final Display display = getShell().getDisplay();
      if (display != null) {
        display.asyncExec(new Runnable()
        {
          public void run()
          {
            try {
              IDE.openEditor(activePage, resource, true);
            } catch (PartInitException e) {
              //              CZTPlugin.log(e);
            }
          }
        });
      }
    }
  }

  /**
   * Subclasses should override to perform the actions of the wizard.
   * This method is run in the wizard container's context as a workspace runnable.
   * @param monitor
   * @throws InterruptedException
   * @throws CoreException
   */
  protected abstract void finishPage(IProgressMonitor monitor)
      throws InterruptedException, CoreException;

  /**
   * Returns the scheduling rule for creating the element.
   */
  protected ISchedulingRule getSchedulingRule()
  {
    return ResourcesPlugin.getWorkspace().getRoot(); // look all by default
  }

  protected boolean canRunForked()
  {
    return false;
  }

  //  public abstract ICZTElement getCreatedElement();

  protected void handleFinishException(Shell shell, InvocationTargetException e)
  {
    String title = "NewWizardMessages.NewElementWizard_op_error_title";
    String message = "NewWizardMessages.NewElementWizard_op_error_message";
    ExceptionHandler.handle(e, shell, title, message);
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.wizard.Wizard#performFinish()
   */
  @Override
  public boolean performFinish()
  {
    IRunnableWithProgress op = new IRunnableWithProgress()
    {
      public void run(IProgressMonitor monitor)
      {
        try {
          finishPage(monitor);
        } catch (CoreException ce) {
          //            CZTPlugin.log("projectWizardCreateError", e);
          throw new OperationCanceledException(ce.getMessage());
        } catch (InterruptedException ie) {
          throw new OperationCanceledException(ie.getMessage());
        }
      }
    };
    try {
      IRunnableWithProgress runnable = new WorkspaceModifyDelegatingOperation(
          op);
      getContainer().run(canRunForked(), true, runnable);
    } catch (InvocationTargetException e) {
      handleFinishException(getShell(), e);
      return false;
    } catch (InterruptedException e) {
      return false;
    }
    return true;
  }

  /* (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench, org.eclipse.jface.viewers.IStructuredSelection)
   */
  public void init(IWorkbench workbench, IStructuredSelection selection)
  {
    fWorkbench = workbench;
    fSelection = selection;
  }

  public IStructuredSelection getSelection()
  {
    return fSelection;
  }

  public IWorkbench getWorkbench()
  {
    return fWorkbench;
  }

  protected void selectAndReveal(IResource newResource)
  {
    BasicNewResourceWizard.selectAndReveal(newResource, fWorkbench
        .getActiveWorkbenchWindow());
  }

}
