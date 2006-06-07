
package net.sourceforge.czt.eclipse.outline;

import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

/**
 * @author Chengdong Xu
 */
public class OutlineLabelProvider extends LabelProvider
    implements
      IColorProvider
{

  //	private static final Image SPECIFICATION_ICON= CZTPluginImages.get(CZTPluginImages.IMG_SPECIFICATION);
  //	private static final Image DEFAULT_ICON = CZTPluginImages.get("sample.gif");

  public OutlineLabelProvider()
  {
    super();
  }

  /**
   * @see ILabelProvider#getText
   */
  public String getText(Object element)
  {
    if (!(element instanceof CztSegment))
      return super.getText(element);

    CztSegment segment = (CztSegment) element;
    return segment.getName();
  }

  /**
   * @see ILabelProvider#getImage
   */
  public Image getImage(Object element)
  {
    //		return null;
    return PlatformUI.getWorkbench().getSharedImages().getImage(
        ISharedImages.IMG_OBJ_ELEMENT);
    //		if (! (element instanceof CztSegment))
    //			return super.getImage(element);

    //		CztSegment segment = (CztSegment) element;

    //		if (segment instanceof Spec)
    //			return SPECIFICATION_ICON;

    //		return DEFAULT_ICON;
  }

  /**
   * @see org.eclipse.jface.viewers.IColorProvider#getForeground(java.lang.Object)
   */
  public Color getForeground(Object element)
  {
    return null;
  }

  /**
   * @see org.eclipse.jface.viewers.IColorProvider#getBackground(java.lang.Object)
   */
  public Color getBackground(Object element)
  {
    return null;
  }
}
