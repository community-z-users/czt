package net.sourceforge.czt.eclipse.zeves.preferences;

import org.eclipse.jface.preference.IPreferenceStore;

import net.sourceforge.czt.eclipse.editors.parser.ZProblemSeverity;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;

public class ZEvesPreferenceConstants {

//	public static final String PROP_GENERATE_FEASIBILITY_VCS = ZEvesPlugin.PLUGIN_ID + ".generateFeasibilityVCs";
	
	private static final String SEVERITY_PREF = ZEvesPlugin.PLUGIN_ID + ".severity";
	
	public static final String SEVERITY_PROOF_COMMAND_PARSE_PROBLEMS = SEVERITY_PREF + ".PROOF_COMMAND_PARSE_PROBLEMS";
	public static final String SEVERITY_PROOF_COMMAND_UNCHECKED_EXPR = SEVERITY_PREF + ".PROOF_COMMAND_UNCHECKED_EXPR";
	public static final String SEVERITY_UNDECIDABLE_SCHEMA_CALCULUS = SEVERITY_PREF + ".UNDECIDABLE_SCHEMA_CALCULUS";
	public static final String SEVERITY_UNDECLARED_NAME_ERROR = SEVERITY_PREF + ".UNDECLARED_NAME_ERROR";
	public static final String SEVERITY_UNKNOWN_TERM = SEVERITY_PREF + ".UNKNOWN_TERM";
	public static final String SEVERITY_TABLE_PROBLEMS = SEVERITY_PREF + ".TABLE_PROBLEMS";
	public static final String SEVERITY_PARENT_PROBLEMS = SEVERITY_PREF + ".PARENT_PROBLEMS";

	public static void initializeDefaultValues(IPreferenceStore store) {
		
		setDefaultSeverityPrefs(store, 
				SEVERITY_PROOF_COMMAND_PARSE_PROBLEMS,
				SEVERITY_PROOF_COMMAND_UNCHECKED_EXPR,
				SEVERITY_UNDECIDABLE_SCHEMA_CALCULUS,
				SEVERITY_UNDECLARED_NAME_ERROR,
				SEVERITY_UNKNOWN_TERM,
				SEVERITY_TABLE_PROBLEMS,
				SEVERITY_PARENT_PROBLEMS);
		
//	    store.setDefault(PROP_GENERATE_FEASIBILITY_VCS, true);
	}
	
	public static ZProblemSeverity getSeverityPref(IPreferenceStore prefs, String prefKey) {
		String value = prefs.getString(prefKey);
		return getSeverity(value);
	}
	
	public static ZProblemSeverity getSeverityDefault(IPreferenceStore prefs, String prefKey) {
		String value = prefs.getDefaultString(prefKey);
		return getSeverity(value);
	}

	private static ZProblemSeverity getSeverity(String value) {
		try {
			return ZProblemSeverity.valueOf(value);
		} catch (Exception ex) {
			// invalid
			return null;
		}
	}
	
	private static void setDefaultSeverityPrefs(IPreferenceStore store, String... prefKeys) {
		for (String prefKey : prefKeys) {
			setDefaultSeverityPref(store, prefKey, ZProblemSeverity.WARNING);
		}
	}
	
	public static void setSeverityPref(IPreferenceStore prefs, String prefKey, ZProblemSeverity severity) {
		prefs.setValue(prefKey, getSeverityKey(severity));
	}

	private static String getSeverityKey(ZProblemSeverity severity) {
		return severity.name();
	}
	
	private static void setDefaultSeverityPref(IPreferenceStore prefs, String prefKey, ZProblemSeverity severity) {
		prefs.setDefault(prefKey, getSeverityKey(severity));
	}
	
}
