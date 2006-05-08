package net.sourceforge.czt.eclipse.editors.zeditor;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.actions.GoToDeclarationAction;
import net.sourceforge.czt.eclipse.editors.parser.ZCompiler;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.BasicTextEditorActionContributor;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class ZEditorActionContributor extends BasicTextEditorActionContributor {

	protected GoToDeclarationAction goToDeclarationAction;
	protected String GoToDeclarationAction_ID = "net.sourceforge.czt.eclipse.editors.actions.GoToDeclaration";
	protected ZCompiler compilerAction;
	protected ITextEditor editor;
	
	/**
	 * Default constructor.
	 */
	public ZEditorActionContributor() {
		super();
		
		goToDeclarationAction= new GoToDeclarationAction(CZTPlugin.getDefault().getResourceBundle(), "GoToDeclaration.", null); //$NON-NLS-1$
		goToDeclarationAction.setActionDefinitionId(this.GoToDeclarationAction_ID);
		compilerAction = ZCompiler.getInstance();
	}
	
	/* (non-Javadoc)
	 * Method declared on EditorActionBarContributor
	 */
	public void contributeToMenu(IMenuManager menuManager) {
		super.contributeToMenu(menuManager);
		IMenuManager editMenu= menuManager.findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);
		
		if (editMenu != null) {
			editMenu.add(goToDeclarationAction);
			editMenu.add(new Separator());
			editMenu.addMenuListener(new IMenuListener() {
				public void menuAboutToShow(IMenuManager m) {
					fillContextMenu(m);
				}
			});
			editMenu.add(goToDeclarationAction);
		}
	}
	
	public void fillContextMenu(IMenuManager menuMgr) {
			ITextSelection selection = (ITextSelection) this.editor
					.getSelectionProvider().getSelection();
			goToDeclarationAction.setEnabled(selection.getLength() > 0);
	}
	
	/* (non-Javadoc)
	 * Method declared on EditorActionBarContributor
	 */
	public void contributeToToolBar(IToolBarManager toolBarManager) {
		super.contributeToToolBar(toolBarManager);
		toolBarManager.add(new Separator());
	}
	
	/* (non-Javadoc)
	 * Method declared on EditorActionBarContributor
	 */
	public void setActiveEditor(IEditorPart part) {
		super.setActiveEditor(part);
		
		if (part instanceof ITextEditor)
			this.editor= (ITextEditor) part;
		goToDeclarationAction.setEditor(this.editor);
//		compilerAction.setEditor(editor);
//		compilerAction.update();
	}
}
