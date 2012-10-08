
package net.sourceforge.czt.eclipse.ui.internal.editors.zeditor;

import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;
import net.sourceforge.czt.eclipse.ui.internal.util.IZMode;
import net.sourceforge.czt.eclipse.ui.internal.util.Selector;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.z.ast.ZName;

import org.eclipse.jface.action.GroupMarker;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IStatusLineManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.action.StatusLineManager;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.texteditor.BasicTextEditorActionContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;
import org.eclipse.ui.texteditor.StatusLineContributionItem;

import static net.sourceforge.czt.eclipse.ui.internal.editors.actions.ICztActionConstants.*;

/**
 * @author Chengdong Xu
 */
public class ZEditorActionContributor extends BasicTextEditorActionContributor
{
  
  /**
   * The name of the status line group item
   */
  private static final String STATUS_LINE_GROUP = "net.sourceforge.czt.eclipse.ui.status.group";
  
  /**
   * The id of the status line contribution item - Editing Mode
   */
  private static final String ID_STATUS_LINE_EDIT_MODE = "net.sourceforge.czt.eclipse.ui.status.edit.mode";
  
  // Display the editor editing mode here
  private StatusLineContributionItem fEditModeArea;
  
  protected ITextEditor fEditor;
  
  private RetargetTextEditorAction fGotoDeclarationAction;
  private RetargetTextEditorAction fHighlightEnclosingTermAction;
  private RetargetTextEditorAction fRestoreLastHighlightAction;
  private RetargetTextEditorAction fConvert2LatexAction;  
  private RetargetTextEditorAction fConvert2OldLatexAction;  
  private RetargetTextEditorAction fConvert2UnicodeAction;  
  private RetargetTextEditorAction fConvert2XMLAction;

  /**
   * Default constructor.
   */
  public ZEditorActionContributor()
  {
    super();
    
    ResourceBundle b= ZEditorMessages.getBundleForActionKeys();
    
    fGotoDeclarationAction = new RetargetTextEditorAction(b, "GotoDeclaration."); //$NON-NLS-1$
    fGotoDeclarationAction.setActionDefinitionId(GO_TO_DECLARATION);
    
    fHighlightEnclosingTermAction = new RetargetTextEditorAction(b, "HighlightEnclosing."); //$NON-NLS-1$
    fHighlightEnclosingTermAction.setActionDefinitionId(HIGHLIGHT_ENCLOSING_ELEMENT);
    
    fRestoreLastHighlightAction = new RetargetTextEditorAction(b, "RestoreLastHighlight."); //$NON-NLS-1$
    fRestoreLastHighlightAction.setActionDefinitionId(RESTORE_LAST_HIGHLIGHT);
    
    fConvert2LatexAction = new RetargetTextEditorAction(b, "Convert2LaTeX."); //$NON-NLS-1$
    fConvert2LatexAction.setActionDefinitionId(CONVERT_TO_LATEX);
    
    fConvert2OldLatexAction = new RetargetTextEditorAction(b, "Convert2OldLaTeX."); //$NON-NLS-1$
    fConvert2OldLatexAction .setActionDefinitionId(CONVERT_TO_OLD_LATEX);
    
    fConvert2UnicodeAction = new RetargetTextEditorAction(b, "Convert2Unicode."); //$NON-NLS-1$
    fConvert2UnicodeAction.setActionDefinitionId(CONVERT_TO_UNICODE);
    
    fConvert2XMLAction = new RetargetTextEditorAction(b, "Convert2XML."); //$NON-NLS-1$
    fConvert2XMLAction.setActionDefinitionId(CONVERT_TO_XML);
    
  }

  /**
   * @see org.eclipse.ui.texteditor.BasicTextEditorActionContributor#contributeToMenu(org.eclipse.jface.action.IMenuManager)
   */
  public void contributeToMenu(IMenuManager menuManager)
  {
    super.contributeToMenu(menuManager);
    IMenuManager editMenu = menuManager
        .findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);

    if (editMenu != null) {
      editMenu.add(fGotoDeclarationAction);
      
      MenuManager highlight = new MenuManager(ZEditorMessages.Editor_HighlightMenu_label, "highlight"); //$NON-NLS-1$
//      editMenu.insertAfter(ActionFactory.SELECT_ALL.getId(), highlight);
      editMenu.add(highlight);
      highlight.add(fHighlightEnclosingTermAction);
      highlight.add(fRestoreLastHighlightAction);
      
      MenuManager convert = new MenuManager(ZEditorMessages.Editor_ConvertMenu_label, "convert");
      editMenu.add(convert);
      convert.add(fConvert2LatexAction);
      convert.add(fConvert2OldLatexAction);
      convert.add(fConvert2UnicodeAction);
      convert.add(fConvert2XMLAction);
      
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
    ITextSelection selection = (ITextSelection) this.fEditor
        .getSelectionProvider().getSelection();
    Selector selector = ((ZEditor) this.fEditor).getParsedData().createTermSelector();
    Term term = selector.getTerm(new Position(selection.getOffset(), selection
        .getLength()));
    
    fGotoDeclarationAction.setEnabled((term != null) && (term instanceof ZName));
    
    fHighlightEnclosingTermAction.setEnabled(true);
    fRestoreLastHighlightAction.setEnabled(((ZEditor) this.fEditor).getTermHighlightAnnotation() != null);
    
    fConvert2LatexAction.setEnabled(!Markup.LATEX.equals(((ZEditor)this.fEditor).getMarkup()));
    fConvert2OldLatexAction.setEnabled(!Markup.LATEX.equals(((ZEditor)this.fEditor).getMarkup()));
    fConvert2UnicodeAction.setEnabled(!Markup.UNICODE.equals(((ZEditor)this.fEditor).getMarkup()));
    fConvert2XMLAction.setEnabled(true);
  }

  
  /**
   * @see org.eclipse.ui.part.EditorActionBarContributor#contributeToToolBar(org.eclipse.jface.action.IToolBarManager)
   */
  public void contributeToToolBar(IToolBarManager toolBarManager)
  {
    super.contributeToToolBar(toolBarManager);
    toolBarManager.add(new Separator());
  }
  
  /**
   * @see org.eclipse.ui.texteditor.BasicTextEditorActionContributor#contributeToStatusLine(org.eclipse.jface.action.IStatusLineManager)
   */
  public void contributeToStatusLine(IStatusLineManager statusLineManager)
  {
    super.contributeToStatusLine(statusLineManager);
    statusLineManager.insertBefore(StatusLineManager.MIDDLE_GROUP, new GroupMarker(STATUS_LINE_GROUP));
    fEditModeArea = new StatusLineContributionItem(ID_STATUS_LINE_EDIT_MODE);
    statusLineManager.appendToGroup(STATUS_LINE_GROUP, fEditModeArea);
    statusLineManager.insertAfter(ID_STATUS_LINE_EDIT_MODE, new Separator());
//    statusLineManager.prependToGroup(StatusLineManager.MIDDLE_GROUP, statusItem);
//    statusLineManager.add(new Separator());
//    statusItem.setText("my status line item");
  }
  
  /**
   * @see org.eclipse.ui.texteditor.BasicTextEditorActionContributor#setActiveEditor(org.eclipse.ui.IEditorPart)
   */
  public void setActiveEditor(IEditorPart part)
  {
    super.setActiveEditor(part);
    if (part instanceof ITextEditor)
      fEditor = (ITextEditor) part;
    
    fGotoDeclarationAction.setAction(getAction(fEditor, GO_TO_DECLARATION));
    
    fHighlightEnclosingTermAction.setAction(getAction(fEditor, HIGHLIGHT_ENCLOSING_ELEMENT));
    fRestoreLastHighlightAction.setAction(getAction(fEditor, RESTORE_LAST_HIGHLIGHT));
    
    fConvert2LatexAction.setAction(getAction(fEditor, CONVERT_TO_LATEX));
    fConvert2OldLatexAction.setAction(getAction(fEditor, CONVERT_TO_OLD_LATEX));
    fConvert2UnicodeAction.setAction(getAction(fEditor, CONVERT_TO_UNICODE));
    fConvert2XMLAction.setAction(getAction(fEditor, CONVERT_TO_XML));
    
//    convert2XMLAction.setEditor(this.editor);
    
/*    
    IHandlerService handlerService =
      (IHandlerService)fEditor.getSite().getService(IHandlerService.class);
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
  */
    
    setEditMode();
  }
  
  private void setEditMode(){
    fEditModeArea.setText(null);
    fEditModeArea.setToolTipText(null);
    if (fEditor == null)
      return;
    if (!(fEditor instanceof ZEditor))
      return;
    String fileType = ((ZEditor)fEditor).getFileType();
    String mode = null;
    if (IZFileType.FILETYPE_LATEX.equals(fileType))
      mode = IZMode.MODE_Z_LATEX;
    else
      mode = IZMode.MODE_Z_UNICODE;
    
    if (mode != null) {
      fEditModeArea.setText(mode);
      fEditModeArea.setToolTipText("The current editing mode is: " + mode);
    }
  }
}
