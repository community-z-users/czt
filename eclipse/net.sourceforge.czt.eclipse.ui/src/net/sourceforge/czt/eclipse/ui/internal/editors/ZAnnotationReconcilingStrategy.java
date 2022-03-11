/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * A reconciling strategy consisting for calculating the annotations for Z specifications.
 * 
 * @author Chengdong Xu
 */
public class ZAnnotationReconcilingStrategy
    implements
      IReconcilingStrategy,
      IReconcilingStrategyExtension
{
  
  private static final Set<String> SCHEMA_PARTITIONS = 
      Collections.unmodifiableSet(new HashSet<String>(Arrays.asList(
          IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF,
          IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH,
          IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA,
          IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF_OLD,
          IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH_OLD,
          IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA_OLD)));
  
  private ITextEditor fEditor;
  
  private String fPartitioning;
  
  private IDocument fDocument;

  private IProgressMonitor fProgressMonitor;
  
  /** holds the calculated positions */
  protected final Map<Position, String> fFoldingPositions = new HashMap<Position, String>();

  /** holds the calculated schema positions */
  protected final List<Position> fSchemaPositions = new ArrayList<Position>();

  private boolean fNotify = true;

  //private IZReconcilingListener fZReconcilingListener;

  //private boolean fIsJavaReconcilingListener;
  
  protected boolean isNotify()
  {
	  return fNotify;
  }
  
  /**
   * 
   */
  public ZAnnotationReconcilingStrategy(ITextEditor editor, String partitioning)
  {
    super();
    fEditor = editor;
    fPartitioning = partitioning;
//    fIsJavaReconcilingListener = fEditor instanceof IZReconcilingListener;
//    if (fIsJavaReconcilingListener)
//      fZReconcilingListener = (IZReconcilingListener) fEditor;
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#setDocument(org.eclipse.jface.text.IDocument)
   */
  public void setDocument(IDocument document)
  {
    fDocument = document;
  }
  
  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#setProgressMonitor(org.eclipse.core.runtime.IProgressMonitor)
   */
  public void setProgressMonitor(IProgressMonitor monitor)
  {
    fProgressMonitor = monitor;
  }
  
  protected IProgressMonitor getIProgressMonitor()
  {
	  return fProgressMonitor;
  }
  

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#initialReconcile()
   */
  public void initialReconcile()
  {
    reconcile(true);
  }
  
  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.IRegion)
   */
  public void reconcile(IRegion partition)
  {
    reconcile(false);
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.reconciler.DirtyRegion, org.eclipse.jface.text.IRegion)
   */
  public void reconcile(DirtyRegion dirtyRegion, IRegion subRegion)
  {
    reconcile(false);
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
//    if (fIsJavaReconcilingListener)
//      fZReconcilingListener.aboutToBeReconciled();
  }

  private void reconcile(final boolean initialReconcile)
  {
    try {
      if (fEditor instanceof ZEditor) {
        SafeRunner.run(new ISafeRunnable()
        {
          public void run()
          {
            try {
              foldPositions();
            } finally {
            }
          }

          public void handleException(Throwable ex)
          {
            IStatus status = new Status(IStatus.ERROR, CztUIPlugin.PLUGIN_ID,
                IStatus.OK, "Error in CZT Core during reconcile", ex); //$NON-NLS-1$
            CztUIPlugin.getDefault().getLog().log(status);
          }
        });

      }
    } finally {
        fNotify = true;
    }
  }

  private void foldPositions()
  {
    fFoldingPositions.clear();
    fSchemaPositions.clear();

    try {
      ITypedRegion[] partitions;
      if (this.fDocument instanceof IDocumentExtension3) {
        IDocumentExtension3 extension3 = (IDocumentExtension3) this.fDocument;
        partitions = extension3.computePartitioning(
            fPartitioning, 0, this.fDocument.getLength(), false);
      }
      else {
        partitions = this.fDocument.computePartitioning(0, this.fDocument
            .getLength());
      }
      
      for (int i = 0; i < partitions.length; i++) {
        ITypedRegion partition = partitions[i];
        int offset = partition.getOffset();
        int length = partition.getLength();
        if (SCHEMA_PARTITIONS.contains(partition.getType())) {
          /*
           * The length of the position for a schema annotation is always 1. Then the drawing strategy
           * will use the fEditor document to access to the corresponding partition area.
           * This may be not a good solution, but a working one.
           */
          fSchemaPositions.add(new Position(offset, length));
        }
        while (length > 0) {
          if (!Character.isWhitespace(this.fDocument.getChar(offset)))
            break;
          offset++;
          length--;
        }
        if (length > 0)
          fFoldingPositions.put(new Position(offset, length), partition.getType());
      }
      
    } catch (BadLocationException ble) {
    } catch (BadPartitioningException bpe) {
    }

    Display.getDefault().asyncExec(new Runnable()
    {
      public void run()
      {
        if (fEditor instanceof ZEditor)
          ((ZEditor) fEditor).updateFoldingStructure(fFoldingPositions);
        if (fEditor instanceof ZEditor)
          ((ZEditor) fEditor).updateSchemaBoxAnnotations(fSchemaPositions);
      }
    });
  }

}
