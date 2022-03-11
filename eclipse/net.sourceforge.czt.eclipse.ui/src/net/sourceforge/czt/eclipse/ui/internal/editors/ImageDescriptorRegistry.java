
package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class ImageDescriptorRegistry
{

  private Map<ImageDescriptor, Image> fRegistry = new HashMap<ImageDescriptor, Image>(10);

  private Display fDisplay;

  /**
   * Creates a new image descriptor registry for the current or default display,
   * respectively.
   */
  public ImageDescriptorRegistry()
  {
    this(SWTUtil.getStandardDisplay());
  }

  /**
   * Creates a new image descriptor registry for the given display. All images
   * managed by this registry will be disposed when the display gets disposed.
   * 
   * @param display the display the images managed by this registry are allocated for 
   */
  public ImageDescriptorRegistry(Display display)
  {
    fDisplay = display;
    Assert.isNotNull(fDisplay);
    hookDisplay();
  }

  /**
   * Returns the image assiciated with the given image descriptor.
   * 
   * @param descriptor the image descriptor for which the registry manages an image
   * @return the image associated with the image descriptor or <code>null</code>
   *  if the image descriptor can't create the requested image.
   */
  public Image get(ImageDescriptor descriptor)
  {
    if (descriptor == null)
      descriptor = ImageDescriptor.getMissingImageDescriptor();

    Image result = (Image) fRegistry.get(descriptor);
    if (result != null)
      return result;

    Assert.isTrue(fDisplay == SWTUtil.getStandardDisplay(),
        "Allocating image for wrong display."); //$NON-NLS-1$
    result = descriptor.createImage();
    if (result != null)
      fRegistry.put(descriptor, result);
    return result;
  }

  /**
   * Disposes all images managed by this registry.
   */
  public void dispose()
  {
    for (Iterator<Image> iter = fRegistry.values().iterator(); iter.hasNext();) {
      Image image = iter.next();
      image.dispose();
    }
    fRegistry.clear();
  }

  private void hookDisplay()
  {
    fDisplay.disposeExec(new Runnable()
    {
      public void run()
      {
        dispose();
      }
    });
  }
}
