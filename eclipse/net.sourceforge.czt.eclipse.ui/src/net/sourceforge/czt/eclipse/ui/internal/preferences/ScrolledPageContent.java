/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.FormColors;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.SharedScrolledComposite;

/**
 * @author Chengdong Xu
 *
 */
public class ScrolledPageContent extends SharedScrolledComposite
{
  private FormToolkit fToolkit;

  public ScrolledPageContent(Composite parent)
  {
    this(parent, SWT.V_SCROLL | SWT.H_SCROLL);
  }

  public ScrolledPageContent(Composite parent, int style)
  {
    super(parent, style);

    setFont(parent.getFont());

    FormColors colors = new FormColors(parent.getDisplay());
    colors.setBackground(null);
    colors.setForeground(null);

    fToolkit = new FormToolkit(colors);

    setExpandHorizontal(true);
    setExpandVertical(true);

    Composite body = new Composite(this, SWT.NONE);
    body.setFont(parent.getFont());
    setContent(body);
  }

  /**
   * @see org.eclipse.swt.widgets.Widget#dispose()
   */
  public void dispose()
  {
    fToolkit.dispose();
    super.dispose();
  }

  public void adaptChild(Control childControl)
  {
    fToolkit.adapt(childControl, true, true);
  }

  public Composite getBody()
  {
    return (Composite) getContent();
  }
}
