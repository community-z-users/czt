package net.sourceforge.czt.eclipse.ui;

import java.net.MalformedURLException;
import java.net.URL;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

/**
 * CZT image definitions.
 * <p>
 * When images are used in label providers (e.g. where {@link Image}) is required, they must be
 * disposed manually. For convenience, {@link org.eclipse.jface.resource.ResourceManager} could
 * be used.
 * </p>
 * 
 * @author Andrius Velykis
 */
public class CztImages
{

  private static final URL ICON_BASE_URL = CztUIPlugin.getDefault().getBundle().getEntry("icons/"); //$NON-NLS-1$

  private static final String T_OBJ = "obj16"; //$NON-NLS-1$

  private static final String T_OVR = "ovr16"; //$NON-NLS-1$

  private static final String T_ELCL = "elcl16"; //$NON-NLS-1$

  private static final ImageDescriptor MISSING_ICON = ImageDescriptor.getMissingImageDescriptor();

  /*
   * Keys for images available from the CZT plug-in image registry.
   */
  public static final ImageDescriptor ZSECTION = createObj("zed16.png"); //$NON-NLS-1$

  public static final ImageDescriptor GIVENPARA = createObj("given16.png"); //$NON-NLS-1$

  public static final ImageDescriptor AXPARA_AXBOX = createObj("axpara16.png"); //$NON-NLS-1$

  public static final ImageDescriptor AXPARA_OMITBOX = createObj("def16.png"); //$NON-NLS-1$

  public static final ImageDescriptor AXPARA_SCHBOX = createObj("schema16.png"); //$NON-NLS-1$

  public static final ImageDescriptor CONJPARA = createObj("conj16.png"); //$NON-NLS-1$

  public static final ImageDescriptor FREEPARA = createObj("free16.png"); //$NON-NLS-1$

  public static final ImageDescriptor OPTEMPPARA = createObj("optemp16.png"); //$NON-NLS-1$

  public static final ImageDescriptor PROOFSCRIPT = createObj("proofscript16.png"); //$NON-NLS-1$

  public static final ImageDescriptor Z_ELEMENT = createObj("zelem16.png"); //$NON-NLS-1$

  public static final ImageDescriptor CHAR_TABLE = createObj("char_table.gif"); //$NON-NLS-1$

  public static final ImageDescriptor COMPLETE_TREE = createElcl("complete_tree.gif"); //$NON-NLS-1$

  public static final ImageDescriptor UNICODE = createElcl("utf.png"); //$NON-NLS-1$

  public static final ImageDescriptor OVR_ERROR = createOvr("error_ovr.gif"); //$NON-NLS-1$

  public static final ImageDescriptor OVR_WARNING = createOvr("warning_ovr.gif"); //$NON-NLS-1$
  
  

  private static ImageDescriptor createObj(String iconPath)
  {
    return create(T_OBJ + "/" + iconPath);
  }

  private static ImageDescriptor createElcl(String iconPath)
  {
    return create(T_ELCL + "/" + iconPath);
  }

  private static ImageDescriptor createOvr(String iconPath)
  {
    return create(T_OVR + "/" + iconPath);
  }

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
