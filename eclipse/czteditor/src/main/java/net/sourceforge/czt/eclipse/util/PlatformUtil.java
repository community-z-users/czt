package net.sourceforge.czt.eclipse.util;

import net.sourceforge.czt.eclipse.CZTPlugin;

import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;

public class PlatformUtil
{

  public static void runInUI(Runnable runnable)
  {
    runInUI(true, runnable);
  }
  
  public static void runInUI(boolean asyncExec, Runnable runnable)
  {

    try {
      Display display = PlatformUI.getWorkbench().getDisplay();

      if (display.isDisposed()) {
        return;
      }

      if (asyncExec) {
        display.asyncExec(runnable);
      } else {
        display.syncExec(runnable);
      }
    }
    catch (IllegalStateException e) {
      // no workbench - just log
      CZTPlugin.log(e);
    }
    
  }

}
