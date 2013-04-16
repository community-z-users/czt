/**
 * The reconciler listens to input document changes as well as changes of the input document of the 
 * text viewer it is installed on. Depending on its configuration it manages the received change 
 * notifications in a queue folding neighboring or overlapping changes together.
 * The reconciler processes the dirty regions as a background activity after having waited for further 
 * changes for the configured duration of time. A reconciler is started using the install(ITextViewer) 
 * method. As a first step initialProcess() is executed in the background. Then, the reconciling thread 
 * waits for changes that need to be reconciled. A reconciler can be resumed by calling forceReconciling()
 * independent from the existence of actual changes. This mechanism is for subclasses only. It is the
 * clients responsibility to stop a reconciler using its uninstall() method. Unstopped reconcilers do
 * not free their resources.
 * It is subclass responsibility to specify how dirty regions are processed.
 * The reconciler is configured with a single reconciling strategy that is used independently from where
 * a dirty region is located in the reconciler's document.
 * Usually, clients instantiate this class and configure it before using it. 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.MonoReconciler;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 *
 */
public class ZReconciler extends MonoReconciler
{

  /** The reconciler's fEditor */
  private ITextEditor fTextEditor;

  /**
   * Tells whether the Z model sent out a changed event.
   */
  private volatile boolean fHasZModelChanged= true;
  
  /**
   * Tells whether this reconciler's fEditor is active.
   */
  private volatile boolean fIsEditorActive = true;

  /**
   * The resource change listener.
   */
  //	private IResourceChangeListener fResourceChangeListener;
  /**
   * Tells whether a reconcile is in progress.
   */
  private volatile boolean fIsReconciling = false;

  private boolean fIninitalProcessDone = false;

  /**
   * The mutex that keeps us from running multiple reconcilers on one editor.
   */
  private Object fMutex;

  /**
   * Creates a new reconciler that uses the same reconciling strategy to reconcile its document 
   * independent of the type of the document's contents.
   * @param fEditor the text fEditor the reconciler is installed on
   * @param strategy the reconciling strategy to be used
   * @param isIncremental the indication whether strategy is incremental or not
   */
  public ZReconciler(ITextEditor editor,
      CZTCompositeReconcilingStrategy strategy, boolean isIncremental)
  {
    super(strategy, isIncremental);
    fTextEditor = editor;

    // https://bugs.eclipse.org/bugs/show_bug.cgi?id=63898
    // when re-using editors, a new reconciler is set up by the source viewer
    // and the old one uninstalled. However, the old reconciler may still be
    // running.
    // To avoid having to reconcilers calling CompilationUnitEditor.reconciled,
    // we synchronized on a lock object provided by the fEditor.
    // The critical section is really the entire run() method of the reconciler
    // thread, but synchronizing process() only will keep JavaReconcilingStrategy
    // from running concurrently on the same fEditor.
    // TODO remove once we have ensured that there is only one reconciler per fEditor.
    if (editor instanceof ZEditor)
      fMutex = ((ZEditor) editor).getReconcilerLock();
    else
      fMutex = new Object(); // Null Object
  }
  
  protected ITextEditor getTextEditor()
  {
	  return fTextEditor;
  }
  
  protected boolean isReconciling()
  {
	  return fIsReconciling;
  }

  /**
   * Tells the reconciler whether any of the available reconciling strategies is interested in 
   * getting detailed dirty region information or just in the fact the the document has been changed.
   * In the second case, the reconciling can not incrementally be pursued. 
   * @param isIncremental indicates whether this reconciler will be configured with incremental 
   * reconciling strategies
   */
  public void setIsIncrementalReconciler(boolean isIncremental)
  {
    super.setIsIncrementalReconciler(isIncremental);
  }

  /**
   * Returns whether any of the reconciling strategies is interested in detailed dirty region information.
   * @return whether this reconciler is incremental
   */
  protected boolean isIncrementalReconciler()
  {
    return super.isIncrementalReconciler();
  }

  /**
   * Installs the reconciler on the given text viewer.
   * After this method has been finished, the reconciler is operational,
   * i.e., it works without requesting further client actions until uninstall is called. 
   * @see org.eclipse.jface.text.reconciler.IReconciler#install(org.eclipse.jface.text.ITextViewer)
   */
  public void install(ITextViewer textViewer)
  {
    super.install(textViewer);
  }

  /**
   * Removes the reconciler from the text viewer it has previously been installed on.
   * @see org.eclipse.jface.text.reconciler.IReconciler#uninstall()
   */
  public void uninstall()
  {
    super.uninstall();
  }

  /**
   * Hook called when the document whose contents should be reconciled has been changed,
   * i.e., the input document of the text viewer this reconciler is installed on.
   * Usually, subclasses use this hook to inform all their reconciling strategies about the change.
   * @param newDocument the new reconciler document
   * @see org.eclipse.jface.text.reconciler.AbstractReconciler#aboutToReconcile()
   * @since 3.0
   */
  protected void reconcilerDocumentChanged(IDocument newDocument)
  {
    super.reconcilerDocumentChanged(newDocument);

//    ZReconcilingStrategy strategy = (ZReconcilingStrategy) getReconcilingStrategy(IDocument.DEFAULT_CONTENT_TYPE);
//    strategy.setEditor(this.fTextEditor);

  }

  /**
   * Starts the reconciler to reconcile the queued dirty-regions.
   */
  protected void startReconciling()
  {
    super.startReconciling();
  }

  /**
   * This method is called on startup of the background activity.
   * It is called only once during the life time of the reconciler.
   * Clients may reimplement this method. 
   * @see org.eclipse.jface.text.reconciler.MonoReconciler#initialProcess()
   */
  protected void initialProcess()
  {
    synchronized (fMutex) {
      super.initialProcess();
    }
    fIninitalProcessDone = true;
  }

  /**
   * Hook for subclasses which want to perform some action as soon as reconciliation is needed.
   * Default implementation is to do nothing. 
   * @see org.eclipse.jface.text.reconciler.AbstractReconciler#aboutToReconcile()
   * @since 3.0
   */
  protected void aboutToBeReconciled()
  {
    CZTCompositeReconcilingStrategy strategy = (CZTCompositeReconcilingStrategy) getReconcilingStrategy(IDocument.DEFAULT_CONTENT_TYPE);
    strategy.aboutToBeReconciled();
  }

  /**
   * Description copied from interface: IReconciler
   * Returns the reconciling strategy registered with the reconciler for the specified content type,
   * or null if there is no such strategy
   * @param contentType the content type for which to determine the reconciling strategy
   * @return the reconciling strategy or null
   */
  public IReconcilingStrategy getReconcilingStrategy(String contentType)
  {
    return super.getReconcilingStrategy(contentType);
  }

  /**
   * Hook that is called after the reconciler thread has been reset.
   * @see org.eclipse.jface.text.reconciler.AbstractReconciler#reconcilerReset()
   */
  protected void reconcilerReset()
  {
    super.reconcilerReset();
    CZTCompositeReconcilingStrategy strategy = (CZTCompositeReconcilingStrategy) getReconcilingStrategy(IDocument.DEFAULT_CONTENT_TYPE);
    strategy.notifyListeners(true);
  }

  /**
   * Processes a dirty region.
   * If the dirty region is null the whole document is consider being dirty.
   * The dirty region is partitioned by the document and each partition is handed over to a 
   * reconciling strategy registered for the partition's content type.
   * @param dirtyRegion the dirty region to be processed
   * @see org.eclipse.jface.text.reconciler.MonoReconciler#process(org.eclipse.jface.text.reconciler.DirtyRegion)
   */
  protected void process(DirtyRegion dirtyRegion)
  {
    synchronized (fMutex) {
      fIsReconciling = true;
      super.process(dirtyRegion);
      fIsReconciling = false;
    }
  }

  /**
   * Returns the input document of the text viewer this reconciler is installed on. 
   * @return the reconciler document
   */
  protected IDocument getDocument()
  {
    return super.getDocument();
  }

  /**
   * Gets the text viewer this reconciler is installed on.
   * @return the text viewer this reconciler is installed on
   */
  protected ITextViewer getTextViewer()
  {
    return super.getTextViewer();
  }

  /**
   * Forces the reconciler to reconcile the structure of the whole document.
   * @see org.eclipse.jface.text.reconciler.AbstractReconciler#forceReconciling()
   */
  protected void forceReconciling()
  {
    if (!fIninitalProcessDone)
      return;

    super.forceReconciling();
    CZTCompositeReconcilingStrategy strategy = (CZTCompositeReconcilingStrategy) getReconcilingStrategy(IDocument.DEFAULT_CONTENT_TYPE);
    strategy.notifyListeners(false);
  }

  /**
     * Tells whether the Z Model has changed or not.
     *
     * @return <code>true</code> iff the Z Model has changed
     * @since 3.0
     */
    protected synchronized boolean hasJavaModelChanged() {
        return fHasZModelChanged;
    }

    /**
     * Sets whether the Z Model has changed or not.
     *
     * @param state <code>true</code> iff the Z model has changed
     * @since 3.0
     */
    protected synchronized void setJavaModelChanged(boolean state) {
        fHasZModelChanged= state;
    }
  // TODO: never used? changed private to protected
    
    
  /**
   * Tells whether this reconciler's fEditor is active.
   *
   * @return <code>true</code> iff the fEditor is active
   * @since 3.1
   */
  protected synchronized boolean isEditorActive()
  {
    return fIsEditorActive;
  }

  /**
   * Sets whether this reconciler's fEditor is active.
   *
   * @param state <code>true</code> iff the fEditor is active
   * @since 3.1
   */
  protected synchronized void setEditorActive(boolean state)
  {
    fIsEditorActive = state;
  }
  // TODO: never used? privete -> protected
}
