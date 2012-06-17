package net.sourceforge.czt.eclipse.zeves.launch;

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
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;


public class ZEvesAppLaunchTab extends ZEvesMainLaunchTab {

	private Text locationField;
	private Button fileLocationButton;
	
	private Spinner portField;

	private WidgetListener fListener= new WidgetListener();
	
	/**
	 * A listener to update for text modification and widget selection.
	 */
	private class WidgetListener extends SelectionAdapter implements ModifyListener {
		
		@Override
		public void modifyText(ModifyEvent e) {
			configModified();
		}
		
		@Override
		public void widgetSelected(SelectionEvent e) {
			setDirty(true);
			Object source= e.getSource();
			if (source == fileLocationButton) {
				handleFileLocationButtonSelected();
			}
		}
		
	}
	
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

		createLocationComponent(mainComposite);
		createConfigComponent(mainComposite);
		createVerticalSpacer(mainComposite, 1);
		
		Dialog.applyDialogFont(parent);
	}

//	protected String getExecutablePath() {
//		
//		if (locationField == null || locationField.isDisposed()) {
//			return "";
//		}
//		
//		return locationField.getText();
//	}

	/**
	 * Creates the controls needed to edit the location attribute of an external tool
	 * 
	 * @param parent the composite to create the controls in
	 */
	private void createLocationComponent(Composite parent) {
		Group group = new Group(parent, SWT.NONE);
		group.setText("Z/Eves executable:");
		group.setLayout(GridLayoutFactory.swtDefaults().create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		locationField = new Text(group, SWT.BORDER);
		locationField.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).hint(IDialogConstants.ENTRY_FIELD_WIDTH, SWT.DEFAULT).create());
		locationField.addModifyListener(fListener);
		addControlAccessibleListener(locationField, group.getText());
		
		Composite buttonComposite = new Composite(group, SWT.NONE);
		buttonComposite.setLayout(GridLayoutFactory.fillDefaults().create());
		buttonComposite.setLayoutData(GridDataFactory.swtDefaults().align(SWT.END, SWT.FILL).create());
		buttonComposite.setFont(parent.getFont());
		
		fileLocationButton= createPushButton(buttonComposite, "Browse File System...", null);
		fileLocationButton.addSelectionListener(fListener);
		addControlAccessibleListener(fileLocationButton, group.getText() + " " + fileLocationButton.getText()); //$NON-NLS-1$
		
	}
	
	/**
	 * Creates the controls needed to edit the port attribute of Z/Eves server
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
		portField.addModifyListener(fListener);
		addControlAccessibleListener(portField, group.getText());
		
		Label portInfoLabel = new Label(group, SWT.WRAP);
		portInfoLabel.setText("Note: Z/Eves prover communication is done via a TCP port.");
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
		
		int port = portField.getSelection();
		configuration.setAttribute(ZEvesLaunchConstants.ATTR_PORT, port);
	}
	
	/**
	 * Validates the contents.
	 */
	@Override
	protected boolean validateConfig(boolean newConfig) {
		String location = locationField.getText().trim();
		if (location.length() < 1) {
			if (newConfig) {
				setErrorMessage(null);
				setMessage("Please specify the executable of Z/Eves theorem prover");
			} else {
				setErrorMessage("Z/Eves executable cannot be empty");
				setMessage(null);
			}
			return false;
		}
		
		return true;
		// sometimes it is not a file, e.g. "wine zeves.exe"
//		File file = new File(location);
//		if (!file.exists()) { // The file does not exist.
//			if (!newConfig) {
//				setErrorMessage("Z/Eves executable does not exist");
//			}
//			return false;
//		}
//		
//		return validateFile(file, newConfig);
	}
	
//	protected boolean validateFile(File file, boolean newConfig) {
//		// must be a file
//		if (!file.isFile()) {
//			if (!newConfig) {
//				setErrorMessage("Z/Eves executable specified is not a file");
//			}
//			return false;
//		}
//		
//		return true;
//	}
	
	/**
	 * Prompts the user to choose a location from the filesystem and sets the
	 * location as the full path of the selected file.
	 */
	private void handleFileLocationButtonSelected() {
		FileDialog dialog = new FileDialog(getShell(), SWT.OPEN);
		dialog.setText("Select Z/Eves Executable");
		dialog.setFilterPath(locationField.getText());
		String text= dialog.open();
		if (text != null) {
			locationField.setText(text);
		}
	}
	
}
