package net.sourceforge.czt.eclipse.ui.internal.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
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
   * @see net.sourceforge.czt.eclipse.ui.internal.editors.actions.ConversionAction#process(net.sourceforge.czt.session.SectionManager)
   */
  @Override
  protected String process(SectionManager manager) throws CommandException
  {
    Key<UnicodeString> key = new Key<UnicodeString>("NEWSECTION", UnicodeString.class);
    UnicodeString unicode = manager.get(key);
    return unicode.toString();
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.internal.editors.actions.ConversionAction#getTargetMarkup()
   */
  @Override
  protected Markup getTargetMarkup()
  {
    return Markup.UNICODE;
  }

}
