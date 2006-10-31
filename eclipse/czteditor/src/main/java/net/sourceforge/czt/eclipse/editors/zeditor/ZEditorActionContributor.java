
package net.sourceforge.czt.eclipse.editors.zeditor;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.actions.AbstractConversionAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2LatexAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2OldLatexAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2UnicodeAction;
import net.sourceforge.czt.eclipse.editors.actions.Convert2XMLAction;
import net.sourceforge.czt.eclipse.editors.actions.ExpandSelectionAction;
import net.sourceforge.czt.eclipse.editors.actions.GoToDeclarationAction;
import net.sourceforge.czt.eclipse.editors.actions.IZEditorActionDefinitionIds;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.z.ast.ZName;

import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.commands.ActionHandler;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.texteditor.BasicTextEditorActionContributor;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class ZEditorActionContributor extends BasicTextEditorActionContributor
{

  protected GoToDeclarationAction goToDeclarationAction;

  protected ExpandSelectionAction expandSelectionAction;

//  protected ContractSelectionAction contractSelectionAction;
  
  protected AbstractConversionAction convert2LatexAction;
  
  protected AbstractConversionAction convert2OldLatexAction;
  
  protected AbstractConversionAction convert2UnicodeAction;
  
  protected AbstractConversionAction convert2XMLAction;

  protected ITextEditor editor;

  /**
   * Default constructor.
   */
  public ZEditorActionContributor()
  {
    super();

    goToDeclarationAction = new GoToDeclarationAction(CZTPlugin.getDefault()
        .getResourceBundle(), "GoToDeclaration.", null); //$NON-NLS-1$
    goToDeclarationAction.setActionDefinitionId(IZEditorActionDefinitionIds.GO_TO_DECLARATION);
    expandSelectionAction = new ExpandSelectionAction(CZTPlugin.getDefault()
        .getResourceBundle(), "ExpandSelection.", null); //$NON-NLS-1$
    expandSelectionAction.setActionDefinitionId(IZEditorActionDefinitionIds.HIGHLIGHT_ENCLOSING_ELEMENT);
//    contractSelectionAction = new ContractSelectionAction(CZTPlugin
//        .getDefault().getResourceBundle(), "ContractSelection.", null); //$NON-NLS-1$
//    contractSelectionAction
//        .setActionDefinitionId(IZEditorActionDefinitionIds.RESTORE_LAST_HIGHLIGHT);
    convert2LatexAction = new Convert2LatexAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2Latex.", null);
    convert2LatexAction.setActionDefinitionId(IZEditorActionDefinitionIds.CONVERT_TO_LATEX);
    convert2OldLatexAction = new Convert2OldLatexAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2OldLatex.", null);
    convert2OldLatexAction.setActionDefinitionId(IZEditorActionDefinitionIds.CONVERT_TO_OLD_LATEX);
    convert2UnicodeAction = new Convert2UnicodeAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2Unicode.", null);
    convert2UnicodeAction.setActionDefinitionId(IZEditorActionDefinitionIds.CONVERT_TO_UNICODE);
    convert2XMLAction = new Convert2XMLAction(CZTPlugin.getDefault()
        .getResourceBundle(), "Convert2XML.", null);
    convert2XMLAction.setActionDefinitionId(IZEditorActionDefinitionIds.CONVERT_TO_XML);
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
//      IContributionItem item = editMenu.find(GoToDeclarationAction_ID);
//      if (item != null)
//        item.setVisible(false);
      
      editMenu.add(goToDeclarationAction);
      editMenu.add(goToDeclarationAction);
      editMenu.add(expandSelectionAction);
      //            editMenu.add(contractSelectionAction);
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
//        && ((term instanceof DeclName) || (term instanceof ZRefName)));
        && (term instanceof ZName));
    expandSelectionAction.setEnabled(true);
//    contractSelectionAction.setEnabled(true);
    convert2LatexAction.setEnabled(!Markup.LATEX.equals(((ZEditor)this.editor).getMarkup()));
    convert2OldLatexAction.setEnabled(!Markup.LATEX.equals(((ZEditor)this.editor).getMarkup()));
    convert2UnicodeAction.setEnabled(!Markup.UNICODE.equals(((ZEditor)this.editor).getMarkup()));
    convert2XMLAction.setEnabled(true);
  }

  /**
   * Method declared on EditorActionBarContributor
   */
  public void contributeToToolBar(IToolBarManager toolBarManager)
  {
    super.contributeToToolBar(toolBarManager);
    toolBarManager.add(new Separator());
  }

  /**
   * Method declared on EditorActionBarContributor
   */
  public void setActiveEditor(IEditorPart part)
  {
    super.setActiveEditor(part);
    if (part instanceof ITextEditor)
      this.editor = (ITextEditor) part;
    
    goToDeclarationAction.setEditor(this.editor);
    expandSelectionAction.setEditor(this.editor);
//    contractSelectionAction.setEditor(this.editor);
    convert2LatexAction.setEditor(this.editor);
    convert2OldLatexAction.setEditor(this.editor);
    convert2UnicodeAction.setEditor(this.editor);
    convert2XMLAction.setEditor(this.editor);
    
    
    IHandlerService handlerService =
      (IHandlerService)editor.getSite().getService(IHandlerService.class);
    handlerService.activateHandler(goToDeclarationAction.getActionDefinitionId(),
      new ActionHandler(goToDeclarationAction));
    handlerService.activateHandler(expandSelectionAction.getActionDefinitionId(),
        new ActionHandler(expandSelectionAction));
 //   handlerService.activateHandler(contractSelectionAction.getActionDefinitionId(),
 //       new ActionHandler(contractSelectionAction));
    handlerService.activateHandler(convert2LatexAction.getActionDefinitionId(),
        new ActionHandler(convert2LatexAction));
    handlerService.activateHandler(convert2OldLatexAction.getActionDefinitionId(),
        new ActionHandler(convert2OldLatexAction));
    handlerService.activateHandler(convert2UnicodeAction.getActionDefinitionId(),
        new ActionHandler(convert2UnicodeAction));
    handlerService.activateHandler(convert2XMLAction.getActionDefinitionId(),
        new ActionHandler(convert2XMLAction));
//    IActionBars bars = getActionBars();
//    bars.setGlobalActionHandler(CZTActionConstants.CONVERT_TO_LATEX, getAction(this.editor, "Convert2Latex"));
  }
}
