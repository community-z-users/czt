package net.sourceforge.czt.eclipse.zeves.ui.launch;

import static net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin.PLUGIN_ID;

public interface ZEvesLaunchConstants {

	/**
	 * String attribute identifying the location of the Z/EVES executable. Default value
	 * is <code>null</code>. 
	 */
	public static final String ATTR_LOCATION = PLUGIN_ID + ".ATTR_LOCATION"; //$NON-NLS-1$
	
	/**
	 * String attribute identifying the working direcory of the Z/EVES executable.
	 * Default value is <code>null</code>. 
	 */
	public static final String ATTR_WORKING_DIR = PLUGIN_ID + ".ATTR_WORKING_DIR"; //$NON-NLS-1$
	
	/**
	 * String attribute identifying Z/EVES server address for remote socket connection.
	 * Default value is <code>null</code>.
	 */
	public static final String ATTR_SERVER_ADDR = PLUGIN_ID + ".ATTR_SERVER_ADDR"; //$NON-NLS-1$

	/**
	 * String attribute identifying the socket port. Default value is
	 * <code>null</code>.
	 */
	public static final String ATTR_PORT = PLUGIN_ID + ".ATTR_PORT"; //$NON-NLS-1$
	
}
