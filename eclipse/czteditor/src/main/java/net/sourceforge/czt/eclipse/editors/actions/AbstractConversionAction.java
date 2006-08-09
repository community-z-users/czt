/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;

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
    String sourceMarkup = editor.getMarkup().toString();
    String targetMarkup = getTargetMarkup();
    String data = null;
    SectionManager manager = editor.getParsedData().getSectionManager();
    try {
      data = process(manager);
    } catch (CommandException e) {
      data = null;
      System.out.println("commandException");
    }
    
    System.out.println(data);
  }
  
  abstract String process(SectionManager manager) throws CommandException;
  
  abstract String getTargetMarkup();
}
