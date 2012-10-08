package net.sourceforge.czt.eclipse.ui.internal.util;

import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchPartSite;

/**
 * <p>
 * An abstract runner class that runs when the given part is next visible. E.g. if the part is
 * already visible, the execution is immediate. Otherwise, the runner is executed the moment it
 * becomes visible.
 * </p>
 * <p>
 * The contents of run are provided by implementing the abstract {@link #run(boolean)} method. The
 * runner is launched with {@link #runWhenNextVisible()} - it will execute either immediately, or
 * when the part becomes visible.
 * </p>
 * <p>
 * If the runner has not been run yet (i.e. is waiting until the part becomes visible), it can be
 * cancelled with {@link #cancel()}.
 * </p>
 * 
 * @author Andrius Velykis
 */
public abstract class VisiblePartRunner extends PartAdapter
{
  
  private IWorkbenchPage fPage;
  private final IWorkbenchPart part;
  private boolean waiting = false;

  public VisiblePartRunner(IWorkbenchPart part)
  {
    this.part = part;
  }

  /**
   * Launch the runner - the code in {@link #run(boolean)} will be executed the first time the part
   * becomes visible. If it is visible when the method is called, it will be run immediately.
   */
  public void runWhenNextVisible()
  {
    if (waiting) {
      // already waiting
      return;
    }
    
    IWorkbenchPartSite site = part.getSite();
    if (site != null) {
      IWorkbenchPage page = site.getPage();
      if (!page.isPartVisible(part)) {
        // if we're not visible - defer until visible
        fPage = page;
        page.addPartListener(this);
        waiting = true;
        return;
      }
    }
    // we're visible - run now
    run(true);
  }
  
  private void doRun(boolean immediate) {
    waiting = false;
    run(immediate);
  }
  
  /**
   * Executes as soon as the given part becomes visible.
   * 
   * @param immediate
   *          whether the execution was immediate - the part was already visible
   */
  protected abstract void run(boolean immediate);

  /**
   * Cancels the run if the runner is waiting for the part to become visible.
   */
  public void cancel()
  {
    // removes the listener from the page
    if (fPage != null) {
      fPage.removePartListener(this);
      fPage = null;
    }
  }

  /*
   * @see org.eclipse.ui.IPartListener2#partVisible(org.eclipse.ui.IWorkbenchPartReference)
   */
  @Override
  public void partVisible(IWorkbenchPartReference partRef)
  {
    if (part.equals(partRef.getPart(false))) {
      cancel();
      doRun(false);
    }
  }

  /*
   * @see org.eclipse.ui.IPartListener2#partClosed(org.eclipse.ui.IWorkbenchPartReference)
   */
  @Override
  public void partClosed(IWorkbenchPartReference partRef)
  {
    if (part.equals(partRef.getPart(false))) {
      cancel();
    }
  }
}
