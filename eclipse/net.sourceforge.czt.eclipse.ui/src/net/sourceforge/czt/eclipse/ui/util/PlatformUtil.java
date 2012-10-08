package net.sourceforge.czt.eclipse.ui.util;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
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
      CztUIPlugin.log(e);
    }
    
  }
  
  /**
   * Retrieves all open editors in the workbench.
   * @return
   */
  public static List<IEditorPart> getOpenEditors()
  {
    List<IEditorPart> editors = new ArrayList<IEditorPart>();
    for (IWorkbenchWindow window : PlatformUI.getWorkbench().getWorkbenchWindows()) {
        for (IWorkbenchPage page : window.getPages()) {
            for (IEditorReference editor : page.getEditorReferences()) {
                IEditorPart editorPart = editor.getEditor(false);
                if (editorPart != null) {
                  // editors can be null if there are problems instantiating them
                  editors.add(editorPart);
                }
            }
        }
    }
    
    return editors;
  }

}
