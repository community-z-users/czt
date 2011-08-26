
package net.sourceforge.czt.eclipse;

import java.net.URL;
import java.util.HashMap;
import java.util.Map.Entry;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.osgi.framework.Bundle;

/**
 * Bundle of most images used by the CZT plug-in.
 * 
 * @author Chengdong Xu
 */
public class CZTPluginImages
{
  //public static final IPath ICONS_PATH= new Path("$nl$/icons/full"); //$NON-NLS-1$
  public static final IPath ICONS_PATH = new Path("$nl$/icons"); //$NON-NLS-1$

  private static final String NAME_PREFIX = "net.sourceforge.czt.eclipse."; //$NON-NLS-1$

  private static final int NAME_PREFIX_LENGTH = NAME_PREFIX.length();

  // The plug-in registry
  private static ImageRegistry fgImageRegistry = null;

  private static HashMap<String, ImageDescriptor> fgAvoidSWTErrorMap = null;

  private static final String T_OBJ = "obj16"; //$NON-NLS-1$

  private static final String T_OVR = "ovr16"; //$NON-NLS-1$
  
  private static final String T_ELCL = "elcl16"; //$NON-NLS-1$

  /*
   * Keys for images available from the CZT plug-in image registry.
   */
  public static final String IMG_ZSECTION = NAME_PREFIX + "zed16.png"; //$NON-NLS-1$

  public static final String IMG_GIVENPARA = NAME_PREFIX + "given16.png"; //$NON-NLS-1$

  public static final String IMG_AXPARA_AXBOX = NAME_PREFIX + "axpara16.png"; //$NON-NLS-1$

  public static final String IMG_AXPARA_OMITBOX = NAME_PREFIX + "def16.png"; //$NON-NLS-1$

  public static final String IMG_AXPARA_SCHBOX = NAME_PREFIX + "schema16.png"; //$NON-NLS-1$

  public static final String IMG_CONJPARA = NAME_PREFIX + "conj16.png"; //$NON-NLS-1$

  public static final String IMG_FREEPARA = NAME_PREFIX + "free16.png"; //$NON-NLS-1$

  public static final String IMG_OPTEMPPARA = NAME_PREFIX + "optemp16.png"; //$NON-NLS-1$
  
  public static final String IMG_PROOFSCRIPT = NAME_PREFIX + "proofscript16.png"; //$NON-NLS-1$
  
  public static final String IMG_Z_ELEMENT = NAME_PREFIX + "zelem16.png"; //$NON-NLS-1$
  
  public static final String IMG_COMPLETE_TREE = NAME_PREFIX + "complete_tree.gif"; //$NON-NLS-1$
  
  public static final String IMG_CHAR_TABLE = NAME_PREFIX + "char_table.gif"; //$NON-NLS-1$

  /*
   * Set of predefined Image Descriptors.
   */
  public static final ImageDescriptor DESC_ZSECTION = createManagedFromKey(
      T_OBJ, IMG_ZSECTION); //$NON-NLS-1$

  public static final ImageDescriptor DESC_GIVENPARA = createManagedFromKey(
      T_OBJ, IMG_GIVENPARA); //$NON-NLS-1$

  public static final ImageDescriptor DESC_AXPARA_AXBOX = createManagedFromKey(
      T_OBJ, IMG_AXPARA_AXBOX); //$NON-NLS-1$

  public static final ImageDescriptor DESC_AXPARA_OMITBOX = createManagedFromKey(
      T_OBJ, IMG_AXPARA_OMITBOX); //$NON-NLS-1$

  public static final ImageDescriptor DESC_AXPARA_SCHBOX = createManagedFromKey(
      T_OBJ, IMG_AXPARA_SCHBOX); //$NON-NLS-1$

  public static final ImageDescriptor DESC_CONJPARA = createManagedFromKey(
      T_OBJ, IMG_CONJPARA); //$NON-NLS-1$

  public static final ImageDescriptor DESC_ZFREEPARA = createManagedFromKey(
      T_OBJ, IMG_FREEPARA); //$NON-NLS-1$

  public static final ImageDescriptor DESC_OPTEMPPARA = createManagedFromKey(
      T_OBJ, IMG_OPTEMPPARA); //$NON-NLS-1$
  
  public static final ImageDescriptor DESC_PROOFSCRIPT = createManagedFromKey(
      T_OBJ, IMG_PROOFSCRIPT); //$NON-NLS-1$
  
  public static final ImageDescriptor DESC_Z_ELEMENT = createManagedFromKey(
      T_OBJ, IMG_Z_ELEMENT); //$NON-NLS-1$
  
  public static final ImageDescriptor DESC_CHAR_TABLE = createManagedFromKey(
      T_OBJ, IMG_CHAR_TABLE); //$NON-NLS-1$
  
  public static final ImageDescriptor DESC_COMPLETE_TREE = createManagedFromKey(
      T_ELCL, IMG_COMPLETE_TREE); //$NON-NLS-1$

  public static final ImageDescriptor DESC_OVR_ERROR = createUnManagedCached(
      T_OVR, "error_ovr.gif"); //$NON-NLS-1$

  public static final ImageDescriptor DESC_OVR_WARNING = createUnManagedCached(
      T_OVR, "warning_ovr.gif"); //$NON-NLS-1$

  // Keys for correction proposal. We have to put the image into the registry since "code assist" doesn't
  // have a life cycle. So no change to dispose icons.

  public static final String IMG_CORRECTION_ADD = NAME_PREFIX
      + "add_correction.gif"; //$NON-NLS-1$

  public static final String IMG_CORRECTION_CAST = NAME_PREFIX
      + "correction_cast.gif"; //$NON-NLS-1$

  static {
    createManagedFromKey(T_OBJ, IMG_CORRECTION_ADD);
    createManagedFromKey(T_OBJ, IMG_CORRECTION_CAST);
  }

  private static final class CachedImageDescriptor extends ImageDescriptor
  {
    private ImageDescriptor fDescriptor;

    private ImageData fData;

    public CachedImageDescriptor(ImageDescriptor descriptor)
    {
      fDescriptor = descriptor;
    }

    public ImageData getImageData()
    {
      if (fData == null) {
        fData = fDescriptor.getImageData();
      }
      return fData;
    }
  }

  /**
   * Returns the image managed under the given key in this registry.
   * 
   * @param key the image's key
   * @return the image managed under the given key
   */
  public static Image get(String key)
  {
    return getImageRegistry().get(key);
  }

  /**
   * Returns the image descriptor for the given key in this registry. Might be called in a non-UI thread.
   * 
   * @param key the image's key
   * @return the image descriptor for the given key
   */
  public static ImageDescriptor getDescriptor(String key)
  {
    if (fgImageRegistry == null) {
      return fgAvoidSWTErrorMap.get(key);
    }
    return getImageRegistry().getDescriptor(key);
  }

  /**
   * Sets the three image descriptors for enabled, disabled, and hovered to an action. The actions
   * are retrieved from the *tool16 folders.
   * 
   * @param action	the action
   * @param iconName	the icon name
   */
  public static void setToolImageDescriptors(IAction action, String iconName)
  {
    setImageDescriptors(action, "tool16", iconName); //$NON-NLS-1$
  }

  /**
   * Sets the three image descriptors for enabled, disabled, and hovered to an action. The actions
   * are retrieved from the *lcl16 folders.
   * 
   * @param action	the action
   * @param iconName	the icon name
   */
  public static void setLocalImageDescriptors(IAction action, String iconName)
  {
    setImageDescriptors(action, "lcl16", iconName); //$NON-NLS-1$
  }

  /*
   * Helper method to access the image registry from the CZTPlugin class.
   */
  /* package */static ImageRegistry getImageRegistry()
  {
    if (fgImageRegistry == null) {
      fgImageRegistry = new ImageRegistry();

      for (Entry<String, ImageDescriptor> entry : fgAvoidSWTErrorMap.entrySet()) {
        fgImageRegistry.put(entry.getKey(), entry.getValue());
      }
      fgAvoidSWTErrorMap = null;

    }

    return fgImageRegistry;
  }

  //---- Helper methods to access icons on the file system --------------------------------------
  private static void setImageDescriptors(IAction action, String type,
      String relPath)
  {
    ImageDescriptor id = create("d" + type, relPath, false); //$NON-NLS-1$
    if (id != null)
      action.setDisabledImageDescriptor(id);

    ImageDescriptor descriptor = create("e" + type, relPath, true); //$NON-NLS-1$
    action.setHoverImageDescriptor(descriptor);
    action.setImageDescriptor(descriptor);
  }

  private static ImageDescriptor createManagedFromKey(String prefix, String key)
  {
    return createManaged(prefix, key.substring(NAME_PREFIX_LENGTH), key);
  }

  private static ImageDescriptor createManaged(String prefix, String name,
      String key)
  {
    ImageDescriptor result = create(prefix, name, true);

    if (fgAvoidSWTErrorMap == null) {
      fgAvoidSWTErrorMap = new HashMap<String, ImageDescriptor>();
    }
    fgAvoidSWTErrorMap.put(key, result);
    if (fgImageRegistry != null) {
      //JavaPlugin.logErrorMessage("Image registry already defined"); //$NON-NLS-1$
    }
    return result;
  }

  /*
   * Creates an image descriptor for the given prefix and name in the JDT UI bundle. The path can
   * contain variables like $NL$.
   * If no image could be found, <code>useMissingImageDescriptor</code> decides if either
   * the 'missing image descriptor' is returned or <code>null</code>.
   * or <code>null</code>.
   */
  private static ImageDescriptor create(String prefix, String name,
      boolean useMissingImageDescriptor)
  {
    IPath path = ICONS_PATH.append(prefix).append(name);
    return createImageDescriptor(CZTPlugin.getDefault().getBundle(), path,
        useMissingImageDescriptor);
  }

  /*
   * Creates an image descriptor for the given prefix and name in the JDT UI bundle. The path can
   * contain variables like $NL$.
   * If no image could be found, the 'missing image descriptor' is returned.
   */
  private static ImageDescriptor createUnManaged(String prefix, String name)
  {
    return create(prefix, name, true);
  }

  /*
   * Creates an image descriptor for the given prefix and name in the JDT UI bundle and let tye descriptor cache the image data.
   * If no image could be found, the 'missing image descriptor' is returned.
   */
  private static ImageDescriptor createUnManagedCached(String prefix,
      String name)
  {
    return new CachedImageDescriptor(create(prefix, name, true));
  }

  /*
   * Creates an image descriptor for the given path in a bundle. The path can contain variables
   * like $NL$.
   * If no image could be found, <code>useMissingImageDescriptor</code> decides if either
   * the 'missing image descriptor' is returned or <code>null</code>.
   * Added for 3.1.1.
   */
  public static ImageDescriptor createImageDescriptor(Bundle bundle,
      IPath path, boolean useMissingImageDescriptor)
  {
    URL url = FileLocator.find(bundle, path, null);
    if (url != null) {
      return ImageDescriptor.createFromURL(url);
    }
    if (useMissingImageDescriptor) {
      return ImageDescriptor.getMissingImageDescriptor();
    }
    return null;
  }
  /*    
   private static URL makeIconFileURL(String prefix, String name)
   throws MalformedURLException
   {
   if (fgIconBaseURL == null)
   throw new MalformedURLException();

   StringBuffer buffer = new StringBuffer(prefix);
   buffer.append('/');
   buffer.append(name);
   
   return new URL(fgIconBaseURL, buffer.toString());
   }

   private static ImageDescriptor create(String prefix, String name)
   {
   try {
   return ImageDescriptor.createFromURL(makeIconFileURL(prefix, name));
   } catch (MalformedURLException e) {
   return ImageDescriptor.getMissingImageDescriptor();
   }
   }
   */
}
