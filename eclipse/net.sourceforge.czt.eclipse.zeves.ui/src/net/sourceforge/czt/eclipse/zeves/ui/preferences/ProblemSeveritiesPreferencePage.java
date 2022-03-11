package net.sourceforge.czt.eclipse.zeves.ui.preferences;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.compile.ZProblemSeverity;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.forms.widgets.Section;
import org.osgi.service.prefs.BackingStoreException;

public class ProblemSeveritiesPreferencePage extends PreferencePage implements
		IWorkbenchPreferencePage {

	private final List<Combo> options = new ArrayList<Combo>();
	private final List<Combo> changedOptions = new ArrayList<Combo>();
	
	private final String[] severityLabels = new String[] { "Error", "Warning", "Ignore" };
	
	public ProblemSeveritiesPreferencePage() {
		super();
	    setPreferenceStore(ZEvesUIPlugin.getDefault().getPreferenceStore());
	    setDescription("Select the severity level for the following optional Z problems:");
	}

	@Override
	public void init(IWorkbench workbench) {}

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
	    
	    Section section = new Section(main, Section.TWISTIE | Section.EXPANDED | Section.CLIENT_INDENT);
	    section.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
	    section.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());
	    
	    section.setText("Z/EVES");
	    
	    Composite sectionGroup = new Composite(section, SWT.NONE);
	    section.setClient(sectionGroup);
	    sectionGroup.setLayout(GridLayoutFactory.swtDefaults().margins(0, 0).numColumns(2).create());
	    
	    createOption(sectionGroup, "Expression problems in proof commands:", 
	    		ZEvesPreferenceConstants.SEVERITY_PROOF_COMMAND_PARSE_PROBLEMS);
	    
	    createOption(sectionGroup, "Unchecked expressions in proof commands:", 
	    		ZEvesPreferenceConstants.SEVERITY_PROOF_COMMAND_UNCHECKED_EXPR);
	    
	    createOption(sectionGroup, "Incompatible theorem references in proof commands:", 
	    		ZEvesPreferenceConstants.SEVERITY_INCOMPATIBLE_THEOREM_REF);
	    
	    createOption(sectionGroup, "Incompatible variable instantiations in proof commands:", 
	    		ZEvesPreferenceConstants.SEVERITY_INCOMPATIBLE_INSTS);
	    
	    createOption(sectionGroup, "Undecidable schema calculus expression within conjecture:", 
	    		ZEvesPreferenceConstants.SEVERITY_UNDECIDABLE_SCHEMA_CALCULUS);
	    
	    createOption(sectionGroup, "Undeclared name in conjecture:", 
	    		ZEvesPreferenceConstants.SEVERITY_UNDECLARED_NAME_ERROR);
	    
            createOption(sectionGroup, "Type mismatch in predicate within conjecture:", 
                ZEvesPreferenceConstants.SEVERITY_PRED_TYPE_MISMATCH);
	    
	    createOption(sectionGroup, "Unchecked binding expressions:", 
                ZEvesPreferenceConstants.SEVERITY_UNCHECKED_BIND_EXPR);
	    
	    createOption(sectionGroup, "Problems in section parent:", 
	    		ZEvesPreferenceConstants.SEVERITY_PARENT_PROBLEMS);

	    createOption(sectionGroup, "Problems in calculating conjecture/proof tables:", 
	    		ZEvesPreferenceConstants.SEVERITY_TABLE_PROBLEMS);
	    
	    createOption(sectionGroup, "Unknown Z term:", 
	    		ZEvesPreferenceConstants.SEVERITY_UNKNOWN_TERM);

	    Dialog.applyDialogFont(main);
	    return main;
	}

	private void createOption(Composite sectionGroup, String label, final String prefKey) {
		
		Label optionLabel = new Label(sectionGroup, SWT.NONE);
		optionLabel.setLayoutData(GridDataFactory.swtDefaults()
				.align(SWT.FILL, SWT.CENTER).grab(true, false).create());
	    optionLabel.setText(label);
	    
	    final Combo optionCombo = new Combo(sectionGroup, SWT.DROP_DOWN | SWT.READ_ONLY);
	    optionCombo.setItems(severityLabels);
	    
	    updateOption(optionCombo, getSeverityPref(prefKey));
	    
	    // set the preference key on the combo
	    optionCombo.setData(prefKey);
	    
	    optionCombo.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				changedOptions.add(optionCombo);
			}
		});
	    
	    options.add(optionCombo);
	}
	
	private void updateOption(Combo optionCombo, ZProblemSeverity severity) {
		// deselect first, then select
		optionCombo.deselect(optionCombo.getSelectionIndex());
		if (severity != null) {
			optionCombo.select(severity.ordinal());
		}
	}
	
	private ZProblemSeverity getSeverityPref(String prefKey) {
		return ZEvesPreferenceConstants.getSeverityPref(getPreferenceStore(), prefKey);
	}
	
	private ZProblemSeverity getSeverityDefault(String prefKey) {
		return ZEvesPreferenceConstants.getSeverityDefault(getPreferenceStore(), prefKey);
	}
	
	private ZProblemSeverity getSelectedSeverity(Combo combo) {
		int selected = combo.getSelectionIndex();
		if (selected >= 0) {
			return ZProblemSeverity.values()[selected];
		}
		
		return null;
	}
	
	@Override
	protected void performDefaults() {
		for (Combo combo : options) {
			String prefKey = (String) combo.getData();
			
			ZProblemSeverity defaultSeverity = getSeverityDefault(prefKey);
			if (getSelectedSeverity(combo) != defaultSeverity) {
				updateOption(combo, defaultSeverity);
				changedOptions.add(combo);
			}
		}

		super.performDefaults();
	}

	@Override
	public boolean performOk() {
		IPreferenceStore store = getPreferenceStore();
		for (Combo combo : changedOptions) {
			String prefKey = (String) combo.getData();
			
			int selected = combo.getSelectionIndex();
			if (selected >= 0) {
				ZProblemSeverity severity = ZProblemSeverity.values()[selected];
				ZEvesPreferenceConstants.setSeverityPref(store, prefKey, severity);
			} else {
				getPreferenceStore().setToDefault(prefKey);
			}
		}
		
		changedOptions.clear();
		
		try {
			InstanceScope.INSTANCE.getNode(ZEvesUIPlugin.PLUGIN_ID).flush();
		} catch (BackingStoreException e) {
			ZEvesUIPlugin.getDefault().log(e);
		}

		return super.performOk();
	}
	
}
