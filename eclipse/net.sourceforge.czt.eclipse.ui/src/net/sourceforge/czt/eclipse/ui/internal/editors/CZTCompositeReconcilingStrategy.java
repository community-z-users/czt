/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Reconciling strategy for CZT code. This is a composite strategy containing the
 * regular Z model reconciler and the annotation strategy.
 * @author Chengdong Xu
 */
public class CZTCompositeReconcilingStrategy
    extends
      CompositeReconcilingStrategy
{
	  // TODO: never used?
	  //private ITextEditor fEditor;

  private ZReconcilingStrategy fZStrategy;

  private ZAnnotationReconcilingStrategy fZAnnotationStrategy;

  /**
   * Creates a new Java reconciling strategy.
   *
   * @param editor the editor of the strategy's reconciler
   * @param partitioning the document partitioning this strategy uses for configuration
   */
  public CZTCompositeReconcilingStrategy(ITextEditor editor, String partitioning)
  {
    //fEditor = editor;
    fZAnnotationStrategy = new ZAnnotationReconcilingStrategy(editor,
        partitioning);
    addReconcilingStrategy(fZAnnotationStrategy);
    fZStrategy = new ZReconcilingStrategy(editor);
    addReconcilingStrategy(fZStrategy);
  }
  
  /**
   * Tells this strategy whether to inform its listeners.
   *
   * @param notify <code>true</code> if listeners should be notified
   */
  public void notifyListeners(boolean notify)
  {
    fZStrategy.notifyListeners(notify);
  }

  /**
   * Called before reconciling is started.
   */
  public void aboutToBeReconciled()
  {
    fZStrategy.aboutToBeReconciled();
  }

}
