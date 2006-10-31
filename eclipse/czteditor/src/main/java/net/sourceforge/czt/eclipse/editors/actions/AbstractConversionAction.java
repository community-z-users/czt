/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.CztUI;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.views.ZConversionView;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;

/**
 * @author Chengdong Xu
 */
public abstract class AbstractConversionAction extends TextEditorAction
{

  /**
   * @param bundle
   * @param prefix
   * @param editor
   */
  public AbstractConversionAction(ResourceBundle bundle, String prefix,
      ITextEditor editor)
  {
    super(bundle, prefix, editor);
  }

  /**
   * @param bundle
   * @param prefix
   * @param editor
   * @param style
   */
  public AbstractConversionAction(ResourceBundle bundle, String prefix,
      ITextEditor editor, int style)
  {
    super(bundle, prefix, editor, style);
  }
  
  public void run() {
    if (!(getTextEditor() instanceof ZEditor))
      return;

    ZEditor editor = (ZEditor) getTextEditor();
    if (editor.getParsedData() == null)
      return;
    String fileName = ((FileEditorInput)editor.getEditorInput()).getName();
    String sourceFileType = editor.getFileType();
    String targetFileType = getTargetFileType();
    String data = null;
    SectionManager manager = editor.getParsedData().getSectionManager();
    try {
      data = process(manager);
    } catch (CommandException e) {
      data = null;
      System.out.println("commandException");
    }
    
    try {
      /*
       * Reveal the Conversion view
       * and ask it to display a particular conversion instance
       */
      IWorkbenchPage page = PlatformUI.getWorkbench()
          .getActiveWorkbenchWindow().getActivePage();
      if (page == null)
        return;
      ZConversionView view = (ZConversionView) page.showView(CztUI.ID_CONVERSIONVIEW);
      view.setConversionData(fileName, sourceFileType, targetFileType, data);
    } catch (PartInitException e) {
      CZTPlugin
          .getDefault()
          .getLog()
          .log(
              new Status(
                  IStatus.ERROR,
                  CztUI.ID_PLUGIN,
                  0,
                  CZTPlugin
                      .getResourceString("CompilerAction.conversionViewOpeningProblem"),
                  e));
    }
  }
  
  abstract String process(SectionManager manager) throws CommandException;
  
  abstract String getTargetFileType();
}
