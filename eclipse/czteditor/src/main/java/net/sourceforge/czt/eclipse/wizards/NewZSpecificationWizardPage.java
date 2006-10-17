/**
 * 
 */

package net.sourceforge.czt.eclipse.wizards;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ContainerSelectionDialog;

/**
 * /**
 * The "New" wizard page allows setting the container for
 * the new file as well as the file name. The page
 * will only accept file name without the extension.
 * 
 * @author Chengdong Xu
 */
public class NewZSpecificationWizardPage extends WizardPage
{

  private Text fContainerText;

  private Text fFileText;

  private final int NUM_OF_MARKUPS = 3;

  private Button[] fMarkupButtons = new Button[NUM_OF_MARKUPS];

  private String[] fMarkupLabels = new String[]{WizardsMessages.NewZSpecificationWizardPage_markupLaTeX, WizardsMessages.NewZSpecificationWizardPage_markupUTF8, WizardsMessages.NewZSpecificationWizardPage_markupUTF16};

  private String[] fExtensions = new String[]{".tex", ".utf8", ".utf16"};
  
  private String[] fSampleFiles = new String[]{"sample_spec_latex.txt", "sample_spec_utf8.txt", "sample_spec_utf16.txt"};

  private IStructuredSelection fSelection;

  private IFile fNewFile;

  private String fWorkspacePath;

  /**
   * @param pageName
   */
  public NewZSpecificationWizardPage(String pageName)
  {
    super(pageName);
  }

  /**
   * @param pageName
   * @param title
   * @param titleImage
   */
  public NewZSpecificationWizardPage(String pageName, String title,
      ImageDescriptor titleImage)
  {
    super(pageName, title, titleImage);
  }

  public NewZSpecificationWizardPage(IStructuredSelection selection)
  {
    super(WizardsMessages.NewZSpecificationWizardPage_name);
    setTitle(WizardsMessages.NewZSpecificationWizardPage_title);
    setDescription(WizardsMessages.NewZSpecificationWizardPage_description);
    this.fSelection = selection;
  }

  /**
   * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
   */
  public void createControl(Composite parent)
  {
    Composite container = new Composite(parent, SWT.NULL);
    FormLayout layout = new FormLayout();
    container.setLayout(layout);
    FormData formData;

    Label containerLabel = new Label(container, SWT.NULL);
    containerLabel.setText(WizardsMessages.NewZSpecificationWizardPage_containerLabel);
    formData = new FormData();
    formData.top = new FormAttachment(0, 5);
    formData.left = new FormAttachment(0, 5);
    containerLabel.setLayoutData(formData);

    Button browseButton = new Button(container, SWT.PUSH);
    browseButton.setText(WizardsMessages.NewZSpecificationWizardPage_browseButtonText);
    formData = new FormData();
    formData.top = new FormAttachment(0, 5);
    formData.right = new FormAttachment(100, -5);
    browseButton.setLayoutData(formData);
    browseButton.addSelectionListener(new SelectionAdapter()
    {
      public void widgetSelected(SelectionEvent e)
      {
        handleBrowse();
      }
    });

    fContainerText = new Text(container, SWT.BORDER | SWT.SINGLE);
    formData = new FormData();
    formData.top = new FormAttachment(0, 5);
    formData.left = new FormAttachment(containerLabel, 5);
    formData.right = new FormAttachment(browseButton, -5);
    fContainerText.setLayoutData(formData);
    fContainerText.addModifyListener(new ModifyListener()
    {
      public void modifyText(ModifyEvent e)
      {
        validate();
      }
    });

    Label fileLabel = new Label(container, SWT.NULL);
    fileLabel.setText(WizardsMessages.NewZSpecificationWizardPage_fileLabel);
    formData = new FormData();
    formData.top = new FormAttachment(containerLabel, 20);
    formData.left = new FormAttachment(0, 5);
    fileLabel.setLayoutData(formData);

    fFileText = new Text(container, SWT.BORDER | SWT.SINGLE);
    formData = new FormData();
    formData.top = new FormAttachment(containerLabel, 20);
    formData.left = new FormAttachment(fileLabel, 5);
    formData.right = new FormAttachment(100, -5);
    fFileText.setLayoutData(formData);
    fFileText.addModifyListener(new ModifyListener()
    {
      public void modifyText(ModifyEvent e)
      {
        validate();
      }
    });

    Group group = new Group(container, SWT.NONE);
    group.setText(WizardsMessages.NewZSpecificationWizardPage_markupLabel);
    GridLayout markupGroupLayout = new GridLayout();
    markupGroupLayout.horizontalSpacing = 5;
    markupGroupLayout.numColumns = 1;
    group.setLayout(markupGroupLayout);

    fMarkupButtons[0] = new Button(group, SWT.RADIO);
    fMarkupButtons[0].setText(fMarkupLabels[0]);
    fMarkupButtons[0].addSelectionListener(new SelectionAdapter() {
      public void widgetSelected(SelectionEvent se) {
        validate();
      }
    });
    fMarkupButtons[1] = new Button(group, SWT.RADIO);
    fMarkupButtons[1].setText(fMarkupLabels[1]);
    fMarkupButtons[1].addSelectionListener(new SelectionAdapter() {
      public void widgetSelected(SelectionEvent se) {
        validate();
      }
    });
    fMarkupButtons[2] = new Button(group, SWT.RADIO);
    fMarkupButtons[2].setText(fMarkupLabels[2]);
    fMarkupButtons[2].addSelectionListener(new SelectionAdapter() {
      public void widgetSelected(SelectionEvent se) {
        validate();
      }
    });

    // set the first markup type to default
    fMarkupButtons[0].setSelection(true);

    formData = new FormData();
    formData.top = new FormAttachment(fileLabel, 20);
    formData.left = new FormAttachment(0, 5);
    formData.right = new FormAttachment(100, -5);
    group.setLayoutData(formData);

    initialize();
    validate();
    setControl(container);

    fWorkspacePath = ResourcesPlugin.getWorkspace().getRoot().getLocation()
        .addTrailingSeparator().toOSString();
  }

  /**
   * Tests if the current workbench selection is a suitable
   * container to use.
   */

  private void initialize()
  {
    if (fSelection != null && !fSelection.isEmpty()) {
      if (fSelection.size() > 1)
        return;
      Object obj = fSelection.getFirstElement();
      if (obj instanceof IResource) {
        IContainer container;
        if (obj instanceof IContainer)
          container = (IContainer) obj;
        else
          container = ((IResource) obj).getParent();
        fContainerText.setText(container.getFullPath().removeTrailingSeparator().toString());
      }
    }
    fFileText.setText(WizardsMessages.NewZSpecificationWizardPage_initSpecName);
  }

  /**
   * Uses the standard container selection dialog to
   * choose the new value for the container field.
   */

  private void handleBrowse()
  {
    ContainerSelectionDialog dialog = new ContainerSelectionDialog(getShell(),
        ResourcesPlugin.getWorkspace().getRoot(), false,
        WizardsMessages.NewZSpecificationWizardPage_selectNewFileContainterTitle);
    if (dialog.open() == ContainerSelectionDialog.OK) {
      Object[] result = dialog.getResult();
      if (result.length == 1) {
        fContainerText.setText(((Path) result[0]).toOSString());
      }
    }
  }

  /**
   * Ensures that both text fields are set.
   */

  private void validate()
  {
    if (fContainerText.getText().trim().length() == 0) {
      updateStatus(WizardsMessages.NewZSpecificationWizardPage_containerMustBeSpecified);
      return;
    }
    if (fFileText.getText().trim().length() == 0) {
      updateStatus(WizardsMessages.NewZSpecificationWizardPage_nameMustbeSpecified);
      return;
    }
    if (checkFolderForExistingFile()) {
      updateStatus(WizardsMessages.NewZSpecificationWizardPage_fileAlreadyExists);
      return;
    }
    int dotLoc = fFileText.getText().indexOf('.');
    if (dotLoc != -1) {
      updateStatus(WizardsMessages.NewZSpecificationWizardPage_invalidDot);
      return;
    }
    updateStatus(null);
  }

  private void updateStatus(String message)
  {
    setErrorMessage(message);
    setPageComplete(message == null);
  }

  public String getContainerName()
  {
    return fContainerText.getText();
  }

  public String getFileName()
  {
    String extension = null;
    for (int i = 0; i < fMarkupButtons.length; i++)
      if (fMarkupButtons[i].getSelection()) {
        extension = fExtensions[i];
        break;
      }

    return fFileText.getText().trim().concat(extension);
  }

  /**
   * @see WizardPage#isPageComplete()
   */
  public boolean isPageComplete()
  {
    return !checkFolderForExistingFile() && super.isPageComplete();
  }

  /**
   * Finds the current directory where the file should be created
   */
  protected boolean checkFolderForExistingFile()
  {
    boolean result = false;

    if (fContainerText.getText() != null) {
      IPath containerPath = new Path(fContainerText.getText().trim());
      if (containerPath.segmentCount() > 1) {
        IFolder container = ResourcesPlugin.getWorkspace().getRoot().getFolder(
            containerPath);
        if (container != null && container.exists()) {
          IResource file = container.getFile(getFileName());
          if (file != null && file.exists()) {
            this.setErrorMessage(WizardsMessages.NewZSpecificationWizardPage_fileAlreadyExists);
            result = true;
          }
        }
      }
      else {
        // this is a project
        IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(
            fContainerText.getText().trim());
        if (project != null && project.exists()) {
          IResource file = project.getFile(getFileName());
          if (file != null && file.exists()) {
            this.setErrorMessage(WizardsMessages.NewZSpecificationWizardPage_fileAlreadyExists);
            result = true;
          }
        }
      }
    }

    //        if (!result)
    //            ((CSharpFileWizard) this.getWizard()).setFileName(fFileText.getText().trim());

    return result;
  }

  protected void performFinish(IProgressMonitor monitor)
  {
    if (monitor == null)
      monitor = new NullProgressMonitor();
    try {
      monitor.beginTask(WizardsMessages.NewZSpecificationWizardPage_specWizard_progressCreating, 5);
      final String containerName = getContainerName();
      final String fileName = getFileName();
      monitor.worked(1);
      createSpecification(containerName, fileName, monitor);
      monitor.worked(4);

      //    } catch (InterruptedException e) {
      //  } catch (InvocationTargetException e) {
      //      Throwable realException = e.getTargetException();
      //      MessageDialog.openError(getShell(), "Wizard.error", realException.getMessage());
    } catch (CoreException e) {
      //          CZTPlugin.log("projectWizardCreateError", e);
      e.printStackTrace();
    } finally {
      monitor.done();
    }
  }

  /**
   * The worker method. It will find the container, create the
   * file if missing or just replace its contents, and open
   * the editor on the newly created file.
   */

  private void createSpecification(String containerName, String fileName,
      IProgressMonitor monitor) throws CoreException
  {
    monitor.beginTask(WizardsMessages.bind(WizardsMessages.NewZSpecificationWizardPage_specWizard_specCreating, fileName), 2);
    IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    IResource resource = root.findMember(new Path(containerName));
    if (!resource.exists() || !(resource instanceof IContainer)) {
      throwCoreException((WizardsMessages.NewZSpecificationWizardPage_specWizard_containerDoesNotExistException)
          + containerName);
    }
    IContainer container = (IContainer) resource;
    final IFile file = container.getFile(new Path(fileName));
    try {
      InputStream stream = openContentStream();
      if (file.exists()) {
        file.setContents(stream, true, true, monitor);
      }
      else {
        file.create(stream, true, monitor);
      }
      stream.close();
    } catch (IOException e) {
    }
    monitor.worked(1);
    monitor.setTaskName((WizardsMessages.NewZSpecificationWizardPage_openingFile));
    monitor.worked(1);

    fNewFile = file;
  }

  /**
   * Initialize file contents with a sample text.
   */
  private InputStream openContentStream()
  {
    if (fMarkupButtons[0].getSelection())
      return getClass().getResourceAsStream(fSampleFiles[0]);
    else if (fMarkupButtons[1].getSelection())
      return getClass().getResourceAsStream(fSampleFiles[1]);
    else if (fMarkupButtons[2].getSelection())
      return getClass().getResourceAsStream(fSampleFiles[2]);
    
    return null;
  }

  private void throwCoreException(String message) throws CoreException
  {
    IStatus status = new Status(IStatus.ERROR, "new.sourceforge.czt.eclipse",
        IStatus.OK, message, null);
    throw new CoreException(status);
  }

  protected IFile getFile()
  {
    return fNewFile;
  }
}
