/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.outline;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.ProblemsLabelDecorator;

import org.eclipse.jface.viewers.DecoratingLabelProvider;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.ILabelDecorator;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.swt.graphics.Color;

/**
 * @author Chengdong Xu
 *
 */
public class DecoratingCztLabelProvider extends DecoratingLabelProvider
    implements
      IColorProvider
{

  //private ProblemsLabelDecorator fLabelDecorator = null;

  /**
   * Decorating label provider for Java. Combines a JavaUILabelProvider
   * with problem and override indicuator with the workbench decorator (label
   * decorator extension point).
   */
  public DecoratingCztLabelProvider(ILabelProvider labelProvider)
  {
    this(labelProvider, true);
  }

  /**
   * Decorating label provider for Java. Combines a JavaUILabelProvider
   * (if enabled with problem indicator) with the workbench
   * decorator (label decorator extension point).
   */
  public DecoratingCztLabelProvider(ILabelProvider labelProvider,
      boolean errorTick)
  {
    //		super(labelProvider, PlatformUI.getWorkbench().getDecoratorManager().getLabelDecorator());
    //		if (errorTick) {
    //			decorator = new ProblemsLabelDecorator(null);
    //			decorator.addListener(labelProvider);
    //			labelProvider.addListener(new ProblemsLabelDecorator(null));
    //		}
    //		super(labelProvider, new ProblemsLabelDecorator(null));
    super(labelProvider, new ProblemsLabelDecorator(CztUIPlugin
        .getImageDescriptorRegistry()));
  }

  public ILabelDecorator getLabelDecorator()
  {
    return super.getLabelDecorator();
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.viewers.IColorProvider#getForeground(java.lang.Object)
   */
  public Color getForeground(Object element)
  {
    // label provider is a OutlineLabelProvider
    return ((IColorProvider) getLabelProvider()).getForeground(element);
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.viewers.IColorProvider#getBackground(java.lang.Object)
   */
  public Color getBackground(Object element)
  {
    // label provider is a OutlineLabelProvider
    return ((IColorProvider) getLabelProvider()).getBackground(element);
  }
}
