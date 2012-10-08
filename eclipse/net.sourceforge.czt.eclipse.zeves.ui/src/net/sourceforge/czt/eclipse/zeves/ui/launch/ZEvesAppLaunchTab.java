package net.sourceforge.czt.eclipse.zeves.ui.launch;

import java.io.File;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;


public class ZEvesAppLaunchTab extends ZEvesMainLaunchTab {

	private Text locationField;
	private Text workingDirField;
	
	private Spinner portField;

  /**
   * A listener to update for text modification and widget selection.
   */
  private final ModifyListener modifyListener = new ModifyListener()
  {
    @Override
    public void modifyText(ModifyEvent e)
    {
      configModified();
    }
  };
	
	/* (non-Javadoc)
	 * @see org.eclipse.debug.ui.ILaunchConfigurationTab#createControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		Composite mainComposite = new Composite(parent, SWT.NONE);
		setControl(mainComposite);
		
		mainComposite.setFont(parent.getFont());
		mainComposite.setLayout(GridLayoutFactory.swtDefaults().create());
		mainComposite.setLayoutData(GridDataFactory.fillDefaults().grab(true, false));

    locationField = createLocationComponent(mainComposite, "Z/EVES executable:",
        new SelectionAdapter()
        {
          @Override
          public void widgetSelected(SelectionEvent e)
          {
            setDirty(true);
            handleFileLocationButtonSelected();
          }
        });
    locationField.addModifyListener(modifyListener);
    workingDirField = createLocationComponent(mainComposite, "Working directory:",
        new SelectionAdapter()
        {
          @Override
          public void widgetSelected(SelectionEvent e)
          {
            setDirty(true);
            handleWorkingDirButtonSelected();
          }
        });
    workingDirField.addModifyListener(modifyListener);
		createConfigComponent(mainComposite);
		createVerticalSpacer(mainComposite, 1);
		
		Dialog.applyDialogFont(parent);
	}

	/**
	 * Creates the controls needed to edit the location attribute of an external tool
	 * 
	 * @param parent the composite to create the controls in
	 */
	private Text createLocationComponent(Composite parent, String label, SelectionListener buttonListener) {
		Group group = new Group(parent, SWT.NONE);
		group.setText(label);
		group.setLayout(GridLayoutFactory.swtDefaults().create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		Text locationField = new Text(group, SWT.BORDER);
		locationField.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).hint(IDialogConstants.ENTRY_FIELD_WIDTH, SWT.DEFAULT).create());
		addControlAccessibleListener(locationField, group.getText());
		
		Composite buttonComposite = new Composite(group, SWT.NONE);
		buttonComposite.setLayout(GridLayoutFactory.fillDefaults().create());
		buttonComposite.setLayoutData(GridDataFactory.swtDefaults().align(SWT.END, SWT.FILL).create());
		buttonComposite.setFont(parent.getFont());
		
		Button fileLocationButton= createPushButton(buttonComposite, "Browse File System...", null);
		fileLocationButton.addSelectionListener(buttonListener);
		addControlAccessibleListener(fileLocationButton, group.getText() + " " + fileLocationButton.getText()); //$NON-NLS-1$
		
		return locationField;
	}
	
	/**
	 * Creates the controls needed to edit the port attribute of Z/EVES server
	 * 
	 * @param parent the composite to create the controls in
	 */
	private void createConfigComponent(Composite parent) {
		Group group = new Group(parent, SWT.NONE);
		group.setLayout(GridLayoutFactory.swtDefaults().numColumns(2).create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		Label portLabel = new Label(group, SWT.NONE);
		portLabel.setText("Port:");
		
		portField = new Spinner(group, SWT.BORDER);
		portField.setMinimum(0);
		portField.setMaximum(65535);
		portField.setPageIncrement(100);
		portField.setLayoutData(GridDataFactory.fillDefaults().hint(IDialogConstants.ENTRY_FIELD_WIDTH, SWT.DEFAULT).create());
		portField.addModifyListener(modifyListener);
		addControlAccessibleListener(portField, group.getText());
		
		Label portInfoLabel = new Label(group, SWT.WRAP);
		portInfoLabel.setText("Note: Z/EVES prover communication is done via a TCP port.");
		portInfoLabel.setLayoutData(GridDataFactory.fillDefaults().span(2, 1).create());
		
	}
	
	/**
	 * Updates the location widgets to match the state of the given launch
	 * configuration.
	 */
	@Override
	protected void updateConfig(ILaunchConfiguration configuration) {
		String location = ZEvesAppLaunch.getLocationConfig(configuration);
		locationField.setText(location);
		
		String workingDir = ZEvesAppLaunch.getWorkingDirConfig(configuration);
                workingDirField.setText(workingDir != null ? workingDir : "");
		
		int port = ZEvesRemoteLaunch.getPortConfig(configuration);
		portField.setSelection(port);
	}

	@Override
	protected void performApplyConfig(ILaunchConfigurationWorkingCopy configuration) {
		String location = locationField.getText().trim();
		if (location.length() == 0) {
			location = null;
		}
		configuration.setAttribute(ZEvesLaunchConstants.ATTR_LOCATION, location);
		
		String workingDir = workingDirField.getText().trim();
                if (workingDir.length() == 0) {
                  workingDir = null;
                }
                configuration.setAttribute(ZEvesLaunchConstants.ATTR_WORKING_DIR, workingDir);
		
		int port = portField.getSelection();
		configuration.setAttribute(ZEvesLaunchConstants.ATTR_PORT, port);
	}
	
	/**
	 * Validates the contents.
	 */
	@Override
	protected boolean validateConfig(boolean newConfig) {
		String location = locationField.getText().trim();
		if (location.isEmpty()) {
			if (newConfig) {
				setErrorMessage(null);
				setMessage("Please specify the executable of Z/EVES theorem prover");
			} else {
				setErrorMessage("Z/EVES executable cannot be empty");
				setMessage(null);
			}
			return false;
		}
		
    String workingDir = workingDirField.getText().trim();
    if (workingDir != null && !workingDir.isEmpty()) {
      // if working dir is specified, check it is an actual directory
      File file = new File(workingDir);
      if (!file.exists()) {
        if (!newConfig) {
          setErrorMessage("Z/EVES working directory does not exist");
        }
        return false;
      }

      // must be a directory
      if (!file.isDirectory()) {
        if (!newConfig) {
          setErrorMessage("Z/EVES working directory is not a directory");
        }
        return false;
      }
    }

    return true;
  }
	
	/**
	 * Prompts the user to choose a location from the filesystem and sets the
	 * location as the full path of the selected file.
	 */
	private void handleFileLocationButtonSelected() {
		FileDialog dialog = new FileDialog(getShell(), SWT.OPEN);
		dialog.setText("Select Z/EVES Executable");
		dialog.setFilterPath(locationField.getText());
		String text= dialog.open();
		if (text != null) {
			locationField.setText(text);
		}
	}
	
  /**
   * Prompts the user to choose a location from the filesystem and sets the
   * working dir as the full path of the selected directory.
   */
  private void handleWorkingDirButtonSelected()
  {
    DirectoryDialog dialog = new DirectoryDialog(getShell());
    dialog.setText("Select Working Directory");
    dialog.setMessage("Select working directory for Z/EVES executable.");
    dialog.setFilterPath(workingDirField.getText());
    String text = dialog.open();
    if (text != null) {
      workingDirField.setText(text);
    }
  }
	
}
