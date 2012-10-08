
package net.sourceforge.czt.eclipse.ui.internal.editors.actions;

import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.NameInfo;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.NameInfoResolver;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.util.Selector;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;

import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;

/**
 * @author Chengdong Xu
 */
public class GoToDeclarationAction extends TextEditorAction
{
  public GoToDeclarationAction(ResourceBundle bundle, String prefix,
      ITextEditor editor)
  {
    super(bundle, prefix, editor);
  }

  public GoToDeclarationAction(ResourceBundle bundle, String prefix,
      ITextEditor editor, int style)
  {
    super(bundle, prefix, editor, style);
  }

  public void run()
  {
    if (!(getTextEditor() instanceof ZEditor))
      return;

    ZEditor editor = (ZEditor) getTextEditor();
    ITextSelection selection = (ITextSelection) editor.getSelectionProvider()
        .getSelection();
    Selector selector = editor.getParsedData().createTermSelector();
    Term term = selector.getTerm(new Position(selection.getOffset(), selection
        .getLength()));
    if (term == null)
      return;
    if (!(term instanceof ZName))
      return;
    ZName decl_term = getDecl(editor.getParsedData(), (ZName) term);
    Position decl_pos = editor.getParsedData().getTermPosition(decl_term);

    if (decl_pos != null) {
      IWorkbenchPage page = CztUIPlugin.getActivePage();
      if (page != null) {
        page.activate(editor);
        editor.selectAndReveal(decl_pos.getOffset(), decl_pos.getLength());
      }
    }
  }

  private ZName getDecl(ParsedData data, ZName ref)
  {
    if (data == null || ref == null)
      return null;

    NameInfo info = NameInfoResolver.findInfo(data.getNameInfoMap(), ref);
    if (info != null)
      return info.getName();

    return getDecl(data.getSpec(), ref);
  }

  private ZName getDecl(Term root, ZName ref)
  {
    if ((root == null) || (ref == null))
      return null;
    if ((ref.getId() == null) || (ref.getWord() == null))
      return null;

    if (root instanceof VarDecl) {
      ZNameList nameList = ((VarDecl) root).getName();
      for (Name name : nameList) {
        if (name instanceof ZName) {
          ZName zName = (ZName) name;
          if (ref.getId().equals(zName.getId())
              && ref.getWord().equals(zName.getWord()))
            return zName;
        }
      }
    }

    for (Object child : root.getChildren()) {
      if (child instanceof Term) {
        ZName result = getDecl((Term) child, ref);
        if (result != null)
          return result;
      }
    }

    return null;
  }
}
