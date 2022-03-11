package net.sourceforge.czt.eclipse.zeves.ui.launch;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTabGroup;
import org.eclipse.debug.ui.CommonTab;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.debug.ui.ILaunchConfigurationTab;


public class ZEvesAppLaunchTabGroup extends AbstractLaunchConfigurationTabGroup {

	@Override
	public void createTabs(ILaunchConfigurationDialog dialog, String mode) {
		
		ILaunchConfigurationTab[] tabs = new ILaunchConfigurationTab[] {
				new ZEvesAppLaunchTab(),
				new CommonTab()
		};
		setTabs(tabs);
	}

}
