package net.sourceforge.czt.eclipse.zeves.launch;

import static net.sourceforge.czt.eclipse.zeves.ZEvesPlugin.PLUGIN_ID;

public interface ZEvesLaunchConstants {

	/**
	 * String attribute identifying the location of the Z/Eves executable. Default value
	 * is <code>null</code>. 
	 */
	public static final String ATTR_LOCATION = PLUGIN_ID + ".ATTR_LOCATION"; //$NON-NLS-1$
	
	/**
	 * String attribute identifying Z/Eves server address for remote socket connection.
	 * Default value is <code>null</code>.
	 */
	public static final String ATTR_SERVER_ADDR = PLUGIN_ID + ".ATTR_SERVER_ADDR"; //$NON-NLS-1$

	/**
	 * String attribute identifying the socket port. Default value is
	 * <code>null</code>.
	 */
	public static final String ATTR_PORT = PLUGIN_ID + ".ATTR_PORT"; //$NON-NLS-1$
	
}