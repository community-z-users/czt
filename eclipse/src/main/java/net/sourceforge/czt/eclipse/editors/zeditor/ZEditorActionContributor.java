package net.sourceforge.czt.eclipse.editors.zeditor;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.actions.ContractSelectionAction;
import net.sourceforge.czt.eclipse.editors.actions.ExpandSelectionAction;
import net.sourceforge.czt.eclipse.editors.actions.GoToDeclarationAction;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.texteditor.BasicTextEditorActionContributor;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class ZEditorActionContributor extends BasicTextEditorActionContributor {

	protected GoToDeclarationAction goToDeclarationAction;
	protected ExpandSelectionAction expandSelectionAction;
	protected ContractSelectionAction contractSelectionAction;
	protected String GoToDeclarationAction_ID = "net.sourceforge.czt.eclipse.editoraction.gotodeclaration";
	protected String ExpandSelectionAction_ID = "net.sourceforge.czt.eclipse.editoraction.expandselection";
	protected String ContractSelectionAction_ID = "net.sourceforge.czt.eclipse.editoraction.contractselection";
	
	protected ITextEditor editor;
	
	/**
	 * Default constructor.
	 */
	public ZEditorActionContributor() {
		super();
		
		goToDeclarationAction = new GoToDeclarationAction(CZTPlugin.getDefault().getResourceBundle(), "GoToDeclaration.", null); //$NON-NLS-1$
		goToDeclarationAction.setActionDefinitionId(this.GoToDeclarationAction_ID);
		expandSelectionAction = new ExpandSelectionAction(CZTPlugin.getDefault().getResourceBundle(), "ExpandSelection.", null); //$NON-NLS-1$
		expandSelectionAction.setActionDefinitionId(this.ExpandSelectionAction_ID);
		contractSelectionAction = new ContractSelectionAction(CZTPlugin.getDefault().getResourceBundle(), "ContractSelection.", null); //$NON-NLS-1$
		contractSelectionAction.setActionDefinitionId(this.ContractSelectionAction_ID);
	}
	
	/* (non-Javadoc)
	 * Method declared on EditorActionBarContributor
	 */
	public void contributeToMenu(IMenuManager menuManager) {
		super.contributeToMenu(menuManager);
		IMenuManager editMenu= menuManager.findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);
		
		if (editMenu != null) {
			editMenu.add(goToDeclarationAction);
			editMenu.add(expandSelectionAction);
//			editMenu.add(contractSelectionAction);
			editMenu.add(new Separator());
			editMenu.addMenuListener(new IMenuListener() {
				public void menuAboutToShow(IMenuManager m) {
					fillContextMenu(m);
				}
			});
		}
	}
	
	public void fillContextMenu(IMenuManager menuMgr) {
			ITextSelection selection = (ITextSelection) this.editor
					.getSelectionProvider().getSelection();
			Selector selector = new Selector(((ZEditor)this.editor).getParsedData().getSpec());
			Term term = selector.getTerm(new Position(selection.getOffset(), selection.getLength()));
			goToDeclarationAction.setEnabled(
					(term != null) && ((term instanceof DeclName) || (term instanceof ZRefName)));
			expandSelectionAction.setEnabled(true);
			contractSelectionAction.setEnabled(true);
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
		expandSelectionAction.setEditor(this.editor);
		contractSelectionAction.setEditor(this.editor);
//		compilerAction.setEditor(editor);
//		compilerAction.update();
	}
}
