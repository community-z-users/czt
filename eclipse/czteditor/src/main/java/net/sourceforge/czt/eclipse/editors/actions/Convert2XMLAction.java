/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class Convert2XMLAction extends AbstractConversionAction
{

  /**
   * @param bundle
   * @param prefix
   * @param editor
   */
  public Convert2XMLAction(ResourceBundle bundle, String prefix,
      ITextEditor editor)
  {
    super(bundle, prefix, editor);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param bundle
   * @param prefix
   * @param editor
   * @param style
   */
  public Convert2XMLAction(ResourceBundle bundle, String prefix,
      ITextEditor editor, int style)
  {
    super(bundle, prefix, editor, style);
  }

  /*
   * @see net.sourceforge.czt.eclipse.editors.actions.AbstractConversionAction#process(net.sourceforge.czt.session.SectionManager)
   */
  @Override
  String process(SectionManager manager) throws CommandException
  {
    Key key = new Key("NEWSECTION", XmlString.class);
    XmlString xml = (XmlString) manager.get(key);
    return xml.toString();
  }

  /*
   * @see net.sourceforge.czt.eclipse.editors.actions.AbstractConversionAction#getTargetMarkup()
   */
  @Override
  String getTargetMarkup()
  {
    return Markup.LATEX.toString();
  }

}
