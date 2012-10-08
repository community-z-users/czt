package net.sourceforge.czt.eclipse.zeves.ui.preferences;

import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

public class ZEvesPreferenceInitializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		IPreferenceStore prefs = ZEvesUIPlugin.getDefault().getPreferenceStore();
		ZEvesPreferenceConstants.initializeDefaultValues(prefs);
	}

}
