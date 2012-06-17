package net.sourceforge.czt.eclipse.zeves.preferences;

import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

public class ZEvesPreferenceInitializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		IPreferenceStore prefs = ZEvesPlugin.getDefault().getPreferenceStore();
		ZEvesPreferenceConstants.initializeDefaultValues(prefs);
	}

}
