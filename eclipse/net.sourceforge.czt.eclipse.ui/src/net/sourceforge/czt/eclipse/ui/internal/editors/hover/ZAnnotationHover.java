
package net.sourceforge.czt.eclipse.ui.internal.editors.hover;

import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.DefaultAnnotationHover;

/**
 * The ZAnnotationHover provides the hover support for Z editors. It is used 
 * for showing popup on annotations on the left and right sides of the editor 
 * (number and overview rulers).
 * <p>
 * The hover extends default one, and displays messages for all annotations. 
 * It excludes annotations specified in 
 * {@link ZTextHover#isIncludedZ(Annotation)}.</p>
 * <p>
 * If the annotation hover does not provide information no hover
 * popup is shown.</p>
 * 
 * @see org.eclipse.jface.text.source.IAnnotationHover
 * @see org.eclipse.jface.text.source.DefaultAnnotationHover
 * 
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZAnnotationHover extends DefaultAnnotationHover
{

  public ZAnnotationHover()
  {
    super();
  }

  public ZAnnotationHover(boolean showLineNumber)
  {
    super(showLineNumber);
  }

  @Override
  protected boolean isIncluded(Annotation annotation)
  {
    return ZTextHover.isIncludedZ(annotation);
  }

}
