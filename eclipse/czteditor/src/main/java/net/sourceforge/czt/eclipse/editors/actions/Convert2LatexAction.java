/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class Convert2LatexAction extends ConversionAction
{

  /**
   * @param bundle
   * @param prefix
   * @param fEditor
   */
  public Convert2LatexAction(ResourceBundle bundle, String prefix,
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
  public Convert2LatexAction(ResourceBundle bundle, String prefix,
      ITextEditor editor, int style)
  {
    super(bundle, prefix, editor, style);
  }

  /**
   * @see net.sourceforge.czt.eclipse.editors.actions.ConversionAction#process(net.sourceforge.czt.session.SectionManager)
   */
  @Override
  String process(SectionManager manager) throws CommandException
  {
    Key key = new Key("NEWSECTION", LatexString.class);
    LatexString latex = (LatexString) manager.get(key);
    return latex.toString();
  }

  /**
   * @see net.sourceforge.czt.eclipse.editors.actions.ConversionAction#getTargetFileType()
   */
  @Override
  String getTargetFileType()
  {
    return IZFileType.FILETYPE_LATEX;
  }
}
