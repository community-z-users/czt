package net.sourceforge.czt.eclipse.zeves.ui.launch;

import net.sourceforge.czt.eclipse.zeves.ui.ZEvesImages;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.swt.accessibility.AccessibleAdapter;
import org.eclipse.swt.accessibility.AccessibleEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Control;

/**
 * @author Andrius Velykis
 */
public abstract class ZEvesMainLaunchTab extends AbstractLaunchConfigurationTab
{

  private final static String FIRST_EDIT = "editedByZEvesTab"; //$NON-NLS-1$
  
  private final ResourceManager resourceManager = new LocalResourceManager(JFaceResources.getResources());

  private boolean fInitializing = false;

  private boolean userEdited = false;

  protected void configModified()
  {
    if (!fInitializing) {
      setDirty(true);
      userEdited = true;
      updateLaunchConfigurationDialog();
    }
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#setDefaults(org.eclipse.debug.core.
   * ILaunchConfigurationWorkingCopy)
   */
  @Override
  public void setDefaults(ILaunchConfigurationWorkingCopy configuration)
  {
    configuration.setAttribute(FIRST_EDIT, true);
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#initializeFrom(org.eclipse.debug.core.ILaunchConfiguration)
   */
  @Override
  public void initializeFrom(ILaunchConfiguration configuration)
  {
    fInitializing = true;
    updateConfig(configuration);
    fInitializing = false;
    setDirty(false);
  }

  protected abstract void updateConfig(ILaunchConfiguration configuration);

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#performApply(org.eclipse.debug.core.ILaunchConfigurationWorkingCopy)
   */
  @Override
  public void performApply(ILaunchConfigurationWorkingCopy configuration)
  {
    performApplyConfig(configuration);

    if (userEdited) {
      configuration.setAttribute(FIRST_EDIT, (String) null);
    }
  }

  protected abstract void performApplyConfig(ILaunchConfigurationWorkingCopy configuration);

  @Override
  public void dispose()
  {
    resourceManager.dispose();
    super.dispose();
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#getName()
   */
  @Override
  public String getName()
  {
    return "Main";
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#isValid(org.eclipse.debug.core.ILaunchConfiguration)
   */
  @Override
  public boolean isValid(ILaunchConfiguration launchConfig)
  {
    setErrorMessage(null);
    setMessage(null);
    boolean newConfig = false;
    try {
      newConfig = launchConfig.getAttribute(FIRST_EDIT, false);
    }
    catch (CoreException e) {
      // assume false is correct
    }

    return validateConfig(newConfig);
  }

  protected abstract boolean validateConfig(boolean newConfig);

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#getImage()
   */
  @Override
  public Image getImage()
  {
    return resourceManager.createImageWithDefault(ZEvesImages.LAUNCH_TAB_ZEVES);
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#deactivated(org.eclipse.debug.core.ILaunchConfigurationWorkingCopy)
   */
  @Override
  public void deactivated(ILaunchConfigurationWorkingCopy workingCopy)
  {
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.debug.ui.ILaunchConfigurationTab#activated(org.eclipse.debug.core.ILaunchConfigurationWorkingCopy)
   */
  @Override
  public void activated(ILaunchConfigurationWorkingCopy workingCopy)
  {
  }

  /*
   * Fix for Bug 60163 Accessibility: New Builder Dialog missing object info for textInput controls
   */
  protected void addControlAccessibleListener(Control control, String controlName)
  {
    // strip mnemonic (&)
    String[] strs = controlName.split("&"); //$NON-NLS-1$
    StringBuffer stripped = new StringBuffer();
    for (int i = 0; i < strs.length; i++) {
      stripped.append(strs[i]);
    }
    control.getAccessible().addAccessibleListener(
        new ControlAccessibleListener(stripped.toString()));
  }


  private class ControlAccessibleListener extends AccessibleAdapter
  {
    private String controlName;

    ControlAccessibleListener(String name)
    {
      controlName = name;
    }

    @Override
    public void getName(AccessibleEvent e)
    {
      e.result = controlName;
    }
  }

}
