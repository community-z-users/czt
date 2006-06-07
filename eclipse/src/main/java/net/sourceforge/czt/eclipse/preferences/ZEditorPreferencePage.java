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
public class ZEditorPreferencePage extends PreferencePage
    implements
      IWorkbenchPreferencePage
{

  /**
   * 
   */
  public ZEditorPreferencePage()
  {
    super();
    // TODO Auto-generated constructor stub
  }

  /**
   * @param title
   */
  public ZEditorPreferencePage(String title)
  {
    super(title);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param title
   * @param image
   */
  public ZEditorPreferencePage(String title, ImageDescriptor image)
  {
    super(title, image);
    // TODO Auto-generated constructor stub
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
   */
  @Override
  protected Control createContents(Composite parent)
  {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
   */
  public void init(IWorkbench workbench)
  {
    // TODO Auto-generated method stub

  }

}
