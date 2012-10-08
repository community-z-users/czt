package net.sourceforge.czt.eclipse.zeves.ui.preferences;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.osgi.service.prefs.BackingStoreException;


public class ZEvesPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {

	private final List<Button> fCheckBoxes = new ArrayList<Button>();
	
	public ZEvesPreferencePage() {
	    super();
	    setPreferenceStore(ZEvesUIPlugin.getDefault().getPreferenceStore());
	    setDescription("Z/EVES theorem prover integration settings.");
	}

	@Override
	public void init(IWorkbench workbench) {}

//	private Button addCheckBox(Composite parent, String label, String tooltip, String key) {
//		GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
//
//		Button button = new Button(parent, SWT.CHECK);
//		button.setText(label);
//		button.setToolTipText(tooltip);
//		button.setData(key);
//		button.setLayoutData(gd);
//
//		button.setSelection(getPreferenceStore().getBoolean(key));
//
//		fCheckBoxes.add(button);
//		return button;
//	}

	@Override
	protected Control createContents(Composite parent) {
		
	    initializeDialogUnits(parent);

	    Composite main = new Composite(parent, SWT.NONE);
	    GridLayout layout = new GridLayout();
	    layout.marginHeight = convertVerticalDLUsToPixels(IDialogConstants.VERTICAL_MARGIN);
	    layout.marginWidth = 0;
	    layout.verticalSpacing = convertVerticalDLUsToPixels(10);
	    layout.horizontalSpacing = convertHorizontalDLUsToPixels(IDialogConstants.HORIZONTAL_SPACING);
	    main.setLayout(layout);
	    
//	    addCheckBox(
//	        main,
//	        "Generate feasibility VCs",
//	        "Generate feasibility verification conditions when paragraphs are submitted to Z/EVES",
//	        ZEvesPreferenceConstants.PROP_GENERATE_FEASIBILITY_VCS);

	    Dialog.applyDialogFont(main);
	    return main;
	}

	@Override
	protected void performDefaults() {
		IPreferenceStore store = getPreferenceStore();
		for (int i = 0; i < fCheckBoxes.size(); i++) {
			Button button = (Button) fCheckBoxes.get(i);
			String key = (String) button.getData();
			button.setSelection(store.getDefaultBoolean(key));
		}

		super.performDefaults();
	}

	@Override
	public boolean performOk() {
		IPreferenceStore store = getPreferenceStore();
		for (int i = 0; i < fCheckBoxes.size(); i++) {
			Button button = (Button) fCheckBoxes.get(i);
			String key = (String) button.getData();
			store.setValue(key, button.getSelection());
		}
		
		try {
			InstanceScope.INSTANCE.getNode(ZEvesUIPlugin.PLUGIN_ID).flush();
		} catch (BackingStoreException e) {
			ZEvesUIPlugin.getDefault().log(e);
		}

		return super.performOk();
	}

}
