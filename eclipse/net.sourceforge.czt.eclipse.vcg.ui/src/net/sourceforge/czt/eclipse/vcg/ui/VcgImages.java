package net.sourceforge.czt.eclipse.vcg.ui;

import java.net.MalformedURLException;
import java.net.URL;


import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;


public class VcgImages {

	/* Declare Common paths */
	private static URL ICON_BASE_URL= null;

	static {
		String pathSuffix = "icons/"; //$NON-NLS-1$	
		ICON_BASE_URL= VcgUIPlugin.getDefault().getBundle().getEntry(pathSuffix);
	}
	
	public static final String IMG_REFRESH = ICON_BASE_URL + "refresh.gif";
	public static final String IMG_INSERT = ICON_BASE_URL + "insert.gif";
	public static final String IMG_IN_SPEC = ICON_BASE_URL + "in_spec.gif";
	
	/**
	 * Returns the <code>Image<code> identified by the given path,
	 * or <code>null</code> if it does not exist.
	 */
	public static Image getImage(String path) {
		ImageRegistry imageRegistry = VcgUIPlugin.getDefault().getImageRegistry();
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
		ImageRegistry imageRegistry = VcgUIPlugin.getDefault().getImageRegistry();
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
