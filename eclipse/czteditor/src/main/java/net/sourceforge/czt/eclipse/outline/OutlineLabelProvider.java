
package net.sourceforge.czt.eclipse.outline;

import net.sourceforge.czt.util.Visitor;

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
  private static Visitor<String> getNodeNameVisitor_ = new NodeNameVisitor();
  //private static Visitor<String> getNodeDescriptionVisitor_ = new NodeDescriptionVisitor();
  private static Visitor<Image> getNodeIconVisitor_ = new NodeIconVisitor();
  
  public OutlineLabelProvider()
  {
    super();
  }

  /**
   * @see ILabelProvider#getText
   */
  public String getText(Object element)
  {
    if (!(element instanceof CztTreeNode))
      return super.getText(element);

    CztTreeNode node = (CztTreeNode) element;
    return node.getTerm().accept(getNodeNameVisitor_);
  }

  /**
   * @see ILabelProvider#getImage
   */
  public Image getImage(Object element)
  {
    if (!(element instanceof CztTreeNode))
      return PlatformUI.getWorkbench().getSharedImages().getImage(
          ISharedImages.IMG_OBJ_ELEMENT);

    CztTreeNode node = (CztTreeNode) element;
    
    Image icon = node.getTerm().accept(getNodeIconVisitor_);
    if (icon == null)
      return PlatformUI.getWorkbench().getSharedImages().getImage(
          ISharedImages.IMG_OBJ_ELEMENT);
    return icon;
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
