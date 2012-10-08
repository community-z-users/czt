package net.sourceforge.czt.eclipse.ui.internal.util;

import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWorkbenchPartReference;

/**
 * A convenience implementation of {@link IPartListener2} with default implementation of all methods
 * as doing nothing. The class should be extended when used and the method of interest overridden.
 * 
 * @author Andrius Velykis
 */
public class PartAdapter implements IPartListener2
{

  @Override
  public void partActivated(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partBroughtToTop(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partClosed(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partDeactivated(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partOpened(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partHidden(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partVisible(IWorkbenchPartReference partRef)
  {
  }

  @Override
  public void partInputChanged(IWorkbenchPartReference partRef)
  {
  }

}
