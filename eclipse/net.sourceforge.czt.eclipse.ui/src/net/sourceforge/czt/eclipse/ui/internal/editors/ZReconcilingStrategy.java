
package net.sourceforge.czt.eclipse.ui.internal.editors;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditorModel;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * A reconciling strategy for parsing Z specifications.
 * 
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZReconcilingStrategy
    implements
      IReconcilingStrategy,
      IReconcilingStrategyExtension
{
  private ITextEditor fEditor;

//  private IDocument fDocument;

  private IProgressMonitor fProgressMonitor;

  private boolean fNotify = true;

  private IZReconcilingListener fZReconcilingListener;

  private boolean fIsZReconcilingListener;

  /**
   * Creates a new, empty composite reconciling strategy.
   */
  public ZReconcilingStrategy(ITextEditor editor)
  {
    super();
    fEditor = editor;
    fIsZReconcilingListener = fEditor instanceof IZReconcilingListener;
    if (fIsZReconcilingListener)
      fZReconcilingListener = (IZReconcilingListener) fEditor;
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#setProgressMonitor(org.eclipse.core.runtime.IProgressMonitor)
   */
  @Override
  public void setProgressMonitor(IProgressMonitor monitor)
  {
    fProgressMonitor = monitor;
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#setDocument(org.eclipse.jface.text.IDocument)
   */
  @Override
  public void setDocument(IDocument document)
  {
//    fDocument = document;
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#initialReconcile()
   */
  @Override
  public void initialReconcile()
  {
    safeReconcile(true);
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.reconciler.DirtyRegion, org.eclipse.jface.text.IRegion)
   */
  @Override
  public void reconcile(DirtyRegion dirtyRegion, IRegion subRegion)
  {
    safeReconcile(false);
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.IRegion)
   */
  @Override
  public void reconcile(IRegion partition)
  {
    safeReconcile(false);
  }

  /**
   * Tells this strategy whether to inform its listeners.
   *
   * @param notify <code>true</code> if listeners should be notified
   */
  public void notifyListeners(boolean notify)
  {
    fNotify = notify;
  }

  /**
   * Called before reconciling is started.
   *
   * @since 3.0
   */
  public void aboutToBeReconciled()
  {
    if (fIsZReconcilingListener)
      fZReconcilingListener.aboutToBeReconciled();
  }

  private void safeReconcile(boolean initialReconcile) {
    try {
      reconcile(initialReconcile);
    } catch (Throwable e) {
      CztUIPlugin.log(e);
      e.printStackTrace();
    } 
  }
  
  private void reconcile(final boolean initialReconcile)
  {
    if (!(fEditor instanceof ZEditor))
      return;
    
    if (!((ZEditor)fEditor).isParsingEnabled())
      return;
    
    ZEditorModel editorModel = ((ZEditor) fEditor).getModel();
    editorModel.reconcile();
    
    // Always notify listeners, see https://bugs.eclipse.org/bugs/show_bug.cgi?id=55969 for the final solution
    try {
      if (fIsZReconcilingListener) {
        IProgressMonitor pm = fProgressMonitor;
        if (pm == null)
          pm = new NullProgressMonitor();
        fZReconcilingListener.reconciled(editorModel.getParsedData(), !fNotify, pm);
      }
    } finally {
      fNotify = true;
    }
  }
}
