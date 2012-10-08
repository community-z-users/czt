package net.sourceforge.czt.eclipse.ui.internal.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.ui.CztUI;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.views.ZConversionView;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;

/**
 * @author Chengdong Xu
 */
public abstract class ConversionAction extends TextEditorAction
{

  /**
   * @param bundle
   * @param prefix
   * @param fEditor
   */
  public ConversionAction(ResourceBundle bundle, String prefix,
      ITextEditor editor)
  {
    super(bundle, prefix, editor);
  }

  /**
   * @param bundle
   * @param prefix
   * @param fEditor
   * @param style
   */
  public ConversionAction(ResourceBundle bundle, String prefix,
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
    Markup sourceMarkup = editor.getMarkup();
    Markup targetMarkup = getTargetMarkup();
    String data = null;
    SectionManager manager = editor.getParsedData().getSectionManager();

    try {
      data = process(manager);
    } catch (Exception e) {
      MessageDialog.openError(getTextEditor().getSite().getShell(), "Conversion Problem",
          "Problems encountered during conversion: " + e.getMessage());
      CztUIPlugin.log(e);
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
      ZConversionView view = (ZConversionView) page.showView(CztUI.CONVERSION_VIEW_ID);
      view.setConversionData(fileName, sourceMarkup, targetMarkup, data);
    } catch (PartInitException e) {
      CztUIPlugin.log(e);
    }
  }
  
  protected abstract String process(SectionManager manager) throws CommandException;
  
  protected abstract Markup getTargetMarkup();
}
