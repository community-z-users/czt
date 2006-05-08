package net.sourceforge.czt.eclipse.editors.actions;

import java.util.Iterator;
import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.parser.Triple;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;

/**
 * @author Chengdong Xu
 */
public class GoToDeclarationAction extends TextEditorAction {

	public GoToDeclarationAction(ResourceBundle bundle, String prefix,
			ITextEditor editor) {
		super(bundle, prefix, editor);
	}

	public GoToDeclarationAction(ResourceBundle bundle, String prefix,
			ITextEditor editor, int style) {
		super(bundle, prefix, editor, style);
	}
	
	public void run() {
		if (!(getTextEditor() instanceof ZEditor))
			return;
		
		ZEditor editor = (ZEditor)getTextEditor();
		Selector selector = editor.getParsedData().getTermSelector();
		ITextSelection selection = (ITextSelection)editor.getSelectionProvider().getSelection();
		Term term = selector.getTerm(new Position(selection.getOffset(), selection.getLength()));
		if (term == null)
			return;
		DeclName decl = null;
		if (term instanceof ZRefName)
			decl = ((ZRefName)term).getDecl();
		
		Position decl_pos = editor.getParsedData().getTermPosition(decl);
		
		if (decl_pos != null) {
			IWorkbenchPage page = CZTPlugin.getActivePage();
			if (page != null) {
				page.activate(editor);
				editor.selectAndReveal(decl_pos.getOffset(), decl_pos.getLength());
			}
		}
	}

}
