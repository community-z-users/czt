package net.sourceforge.czt.eclipse.zeves.ui;

import java.net.MalformedURLException;
import java.net.URL;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

/**
 * Z/EVES image definitions.
 * <p>
 * When images are used in label providers (e.g. where {@link Image}) is required, they must be
 * disposed manually. For convenience, {@link org.eclipse.jface.resource.ResourceManager} could
 * be used.
 * </p>
 * 
 * @author Andrius Velykis
 */
public class ZEvesImages {
  
  private static final URL ICON_BASE_URL = ZEvesUIPlugin.getDefault().getBundle().getEntry("icons/"); //$NON-NLS-1$
  
  private static final ImageDescriptor MISSING_ICON = ImageDescriptor.getMissingImageDescriptor();
  
  public static final ImageDescriptor LAUNCH_TAB_ZEVES = create("z-eves.png");
  public static final ImageDescriptor REFRESH = create("refresh.gif");
  public static final ImageDescriptor RESET = create("reset.gif");
  public static final ImageDescriptor OUTPUT_SELECTION = create("output_selection.gif");
  
  public static final ImageDescriptor THEOREM_AXIOM = create("conj.png");
  public static final ImageDescriptor THEOREM_GOAL = create("conj16.png");
  
  public static final ImageDescriptor THEOREM_PROVED = create("thm_proved.gif");
  public static final ImageDescriptor THEOREM_UNPROVED = create("thm_unproved.gif");
  
  
  private static ImageDescriptor create(String iconPath)
  {
    try {
      final URL url = new URL(ICON_BASE_URL, iconPath);
      return ImageDescriptor.createFromURL(url);
    }
    catch (MalformedURLException e) {
      return MISSING_ICON;
    }
  }

}
