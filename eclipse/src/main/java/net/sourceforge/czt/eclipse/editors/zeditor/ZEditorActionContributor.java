
package net.sourceforge.czt.eclipse.editors.zeditor;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.actions.AbstractConversionAction;
import net.sourceforge.czt.eclipse.editors.actions.ContractSelectionAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2LatexAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2OldLatexAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2UnicodeAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2XMLAction;
import net.sourceforge.czt.eclipse.editors.actions.ExpandSelectionAction;
import net.sourceforge.czt.eclipse.editors.actions.GoToDeclarationAction;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.jface.action.IContributionItem;
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
public class ZEditorActionContributor extends BasicTextEditorActionContributor
{

  protected GoToDeclarationAction goToDeclarationAction;

  protected ExpandSelectionAction expandSelectionAction;

  protected ContractSelectionAction contractSelectionAction;
  
  protected AbstractConversionAction convert2LatexAction;
  
  protected AbstractConversionAction convert2OldLatexAction;
  
  protected AbstractConversionAction convert2UnicodeAction;
  
  protected AbstractConversionAction convert2XMLAction;

  protected String GoToDeclarationAction_ID = "net.sourceforge.czt.eclipse.editoraction.gotodeclaration";
  protected String ExpandSelectionAction_ID = "net.sourceforge.czt.eclipse.editoraction.expandselection";
  protected String ContractSelectionAction_ID = "net.sourceforge.czt.eclipse.editoraction.contractselection";
  protected String Convert2LatexAction_ID = "net.sourceforge.czt.eclipse.editoraction.convert2latex";
  protected String Convert2OldLatexAction_ID = "net.sourceforge.czt.eclipse.editoraction.convert2latex";
  protected String Convert2UnicodeAction_ID = "net.sourceforge.czt.eclipse.editoraction.convert2latex";
  protected String Convert2XMLAction_ID = "net.sourceforge.czt.eclipse.editoraction.convert2latex";

  protected ITextEditor editor;

  /**
   * Default constructor.
   */
  public ZEditorActionContributor()
  {
    super();

    goToDeclarationAction = new GoToDeclarationAction(CZTPlugin.getDefault()
        .getResourceBundle(), "GoToDeclaration.", null); //$NON-NLS-1$
    goToDeclarationAction.setActionDefinitionId(this.GoToDeclarationAction_ID);
    expandSelectionAction = new ExpandSelectionAction(CZTPlugin.getDefault()
        .getResourceBundle(), "ExpandSelection.", null); //$NON-NLS-1$
    expandSelectionAction.setActionDefinitionId(this.ExpandSelectionAction_ID);
    contractSelectionAction = new ContractSelectionAction(CZTPlugin
        .getDefault().getResourceBundle(), "ContractSelection.", null); //$NON-NLS-1$
    contractSelectionAction
        .setActionDefinitionId(this.ContractSelectionAction_ID);
    convert2LatexAction = new Convert2LatexAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2Latex.", null);
    convert2LatexAction.setActionDefinitionId(this.Convert2LatexAction_ID);
    convert2OldLatexAction = new Convert2OldLatexAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2OldLatex.", null);
    convert2OldLatexAction.setActionDefinitionId(this.Convert2OldLatexAction_ID);
    convert2UnicodeAction = new Convert2UnicodeAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2Unicode.", null);
    convert2UnicodeAction.setActionDefinitionId(this.Convert2UnicodeAction_ID);
    convert2XMLAction = new Convert2XMLAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2XML.", null);
    convert2XMLAction.setActionDefinitionId(this.Convert2XMLAction_ID);
    
  }

  /**
   * Method declared on EditorActionBarContributor
   */
  public void contributeToMenu(IMenuManager menuManager)
  {
    super.contributeToMenu(menuManager);
    IMenuManager editMenu = menuManager
        .findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);

    if (editMenu != null) {
      IContributionItem item = editMenu.find(GoToDeclarationAction_ID);
      if (item != null)
        item.setVisible(false);
      editMenu.add(goToDeclarationAction);
      editMenu.add(expandSelectionAction);
      //			editMenu.add(contractSelectionAction);
      editMenu.add(convert2LatexAction);
      editMenu.add(convert2OldLatexAction);
      editMenu.add(convert2UnicodeAction);
      editMenu.add(convert2XMLAction);
      editMenu.add(new Separator());
      editMenu.addMenuListener(new IMenuListener()
      {
        public void menuAboutToShow(IMenuManager m)
        {
          fillContextMenu(m);
        }
      });
    }
  }

  public void fillContextMenu(IMenuManager menuMgr)
  {
    ITextSelection selection = (ITextSelection) this.editor
        .getSelectionProvider().getSelection();
    Selector selector = new Selector(((ZEditor) this.editor).getParsedData()
        .getSpec());
    Term term = selector.getTerm(new Position(selection.getOffset(), selection
        .getLength()));
    goToDeclarationAction.setEnabled((term != null)
        && ((term instanceof DeclName) || (term instanceof ZRefName)));
    expandSelectionAction.setEnabled(true);
    contractSelectionAction.setEnabled(true);
    
    convert2LatexAction.setEnabled(true);
    convert2OldLatexAction.setEnabled(true);
    convert2UnicodeAction.setEnabled(true);
    convert2XMLAction.setEnabled(true);
  }

  /* (non-Javadoc)
   * Method declared on EditorActionBarContributor
   */
  public void contributeToToolBar(IToolBarManager toolBarManager)
  {
    super.contributeToToolBar(toolBarManager);
    toolBarManager.add(new Separator());
  }

  /* (non-Javadoc)
   * Method declared on EditorActionBarContributor
   */
  public void setActiveEditor(IEditorPart part)
  {
    super.setActiveEditor(part);

    if (part instanceof ITextEditor)
      this.editor = (ITextEditor) part;
    goToDeclarationAction.setEditor(this.editor);
    expandSelectionAction.setEditor(this.editor);
    contractSelectionAction.setEditor(this.editor);
    convert2LatexAction.setEditor(this.editor);
    convert2OldLatexAction.setEditor(this.editor);
    convert2UnicodeAction.setEditor(this.editor);
    convert2XMLAction.setEditor(this.editor);
    //		compilerAction.setEditor(editor);
    //		compilerAction.update();
  }
}
