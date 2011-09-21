package net.sourceforge.czt.eclipse.zeves;

import java.net.MalformedURLException;
import java.net.URL;


import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;


public class ZEvesImages {

	/* Declare Common paths */
	private static URL ICON_BASE_URL= null;

	static {
		String pathSuffix = "icons/"; //$NON-NLS-1$	
		ICON_BASE_URL= ZEvesPlugin.getDefault().getBundle().getEntry(pathSuffix);
	}
	
	public static final String IMG_LAUNCH_TAB_ZEVES = ICON_BASE_URL + "z-eves.png";
	public static final String IMG_REFRESH = ICON_BASE_URL + "refresh.gif";
	public static final String IMG_RESET = ICON_BASE_URL + "reset.gif";
	public static final String IMG_OUTPUT_SELECTION = ICON_BASE_URL + "output_selection.gif";
	
	public static final String IMG_THEOREM_AXIOM = ICON_BASE_URL + "conj.png";
	public static final String IMG_THEOREM_GOAL = ICON_BASE_URL + "conj16.png";
	
	public static final String IMG_THEOREM_PROVED = ICON_BASE_URL + "thm_proved.gif";
	public static final String IMG_THEOREM_UNPROVED = ICON_BASE_URL + "thm_unproved.gif";
	
	/**
	 * Returns the <code>Image<code> identified by the given path,
	 * or <code>null</code> if it does not exist.
	 */
	public static Image getImage(String path) {
		ImageRegistry imageRegistry = ZEvesPlugin.getDefault().getImageRegistry();
		Image image = imageRegistry.get(path);
		if (image == null) {
			getImageDescriptor(path);
			image = imageRegistry.get(path);
		}
		
		return image;
	}
	
	/**
	 * Returns the <code>ImageDescriptor<code> identified by the given path,
	 * or <code>null</code> if it does not exist.
	 */
	public static ImageDescriptor getImageDescriptor(String path) {
		ImageRegistry imageRegistry = ZEvesPlugin.getDefault().getImageRegistry();
		ImageDescriptor desc = imageRegistry.getDescriptor(path);
		if (desc == null) {
			desc = ImageDescriptor.getMissingImageDescriptor();
			try {
				desc = ImageDescriptor.createFromURL(new URL(path));
				imageRegistry.put(path, desc);
			} catch (MalformedURLException me) {
			}
		}
		
		return desc;
	}
	
}
