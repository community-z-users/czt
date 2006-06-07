/**
 * 
 */

package net.sourceforge.czt.eclipse.preferences;

import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author Chengdong Xu
 *
 */
public class AppearancePreferencePage extends PreferencePage
    implements
      IWorkbenchPreferencePage
{

  /**
   * 
   */
  public AppearancePreferencePage()
  {
    super();
  }

  /**
   * @param title
   */
  public AppearancePreferencePage(String title)
  {
    super(title);
  }

  /**
   * @param title
   * @param image
   */
  public AppearancePreferencePage(String title, ImageDescriptor image)
  {
    super(title, image);
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
   */
  @Override
  protected Control createContents(Composite parent)
  {
    return null;
  }

  /* (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
   */
  public void init(IWorkbench workbench)
  {

  }

}
