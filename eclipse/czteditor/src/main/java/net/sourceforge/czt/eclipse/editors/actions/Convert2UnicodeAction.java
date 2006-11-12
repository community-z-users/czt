/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class Convert2UnicodeAction extends ConversionAction
{

  /**
   * @param bundle
   * @param prefix
   * @param fEditor
   */
  public Convert2UnicodeAction(ResourceBundle bundle, String prefix,
      ITextEditor editor)
  {
    super(bundle, prefix, editor);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param bundle
   * @param prefix
   * @param fEditor
   * @param style
   */
  public Convert2UnicodeAction(ResourceBundle bundle, String prefix,
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
    Key key = new Key("NEWSECTION", UnicodeString.class);
    UnicodeString unicode = (UnicodeString) manager.get(key);
    return unicode.toString();
  }

  /**
   * @see net.sourceforge.czt.eclipse.editors.actions.ConversionAction#getTargetMarkup()
   */
  @Override
  String getTargetFileType()
  {
    return IZFileType.FILETYPE_UTF8;
  }

}
