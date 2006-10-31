
package net.sourceforge.czt.eclipse.editors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.parser.ZCompiler;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;

import org.eclipse.core.runtime.IProgressMonitor;
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
 * A reconciling strategy consisting of a sequence of internal reconciling strategies.
 * By default, all requests are passed on to the contained strategies.
 *
 * @since 3.0
 * @author Chengdong Xu
 */
public class ZReconcilingStrategy
    implements
      IReconcilingStrategy,
      IReconcilingStrategyExtension
{

  private ITextEditor fTextEditor;

  /** holds the calculated positions */
  protected final List<Position> fPositions = new ArrayList<Position>();
  
  /** holds the calculated schema positions */
  protected final List<Position> fSchemaPositions = new ArrayList<Position>();
  
  private IDocument fDocument;

  /** The offset of the next character to be read */
  protected int fOffset;

  /** The end offset of the range to be scanned */
  protected int fRangeEnd;

  protected IReconcilingStrategy[] fStrategies;

  /**
   * Creates a new, empty composite reconciling strategy.
   */
  public ZReconcilingStrategy()
  {
    super();
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#setProgressMonitor(org.eclipse.core.runtime.IProgressMonitor)
   */
  public void setProgressMonitor(IProgressMonitor monitor)
  {
    //		setProgressMonitor(monitor);
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#setDocument(org.eclipse.jface.text.IDocument)
   */
  public void setDocument(IDocument document)
  {
    this.fDocument = document;
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#initialReconcile()
   */
  public void initialReconcile()
  {
    final ITextEditor editor = getEditor();
    if (editor instanceof ZEditor) {
      foldPositions();
      ZCompiler compiler = ZCompiler.getInstance();
      if (compiler != null) {
        compiler.setEditor((ZEditor) editor);
        final ParsedData data = compiler.parse();
        ((ZEditor) editor).setParsedData(data);
        ((ZEditor) editor).updateOutlinePage(data);
      }

    }
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.reconciler.DirtyRegion, org.eclipse.jface.text.IRegion)
   */
  public void reconcile(DirtyRegion dirtyRegion, IRegion subRegion)
  {
    initialReconcile();
  }

  /**
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.IRegion)
   */
  public void reconcile(IRegion partition)
  {
    initialReconcile();
  }

  /**
   * Sets the reconciling strategies for this composite strategy.
   *
   * @param strategies the strategies to be set or <code>null</code>
   */
  public void setReconcilingStrategies(IReconcilingStrategy[] strategies)
  {
    fStrategies = strategies;
  }

  /**
   * Returns the previously set stratgies or <code>null</code>.
   *
   * @return the contained strategies or <code>null</code>
   */
  public IReconcilingStrategy[] getReconcilingStrategies()
  {
    return fStrategies;
  }

  public ITextEditor getEditor()
  {
    return this.fTextEditor;
  }

  public void setEditor(ITextEditor editor)
  {
    this.fTextEditor = editor;
  }

  /**
   * next character position - used locally and only valid while
   * {@link #foldPositions()} is in progress.
   */
  protected int cNextPos = 0;

  /**
   * uses {@link #fDocument}, {@link #fOffset} and {@link #fRangeEnd} to
   * calculate {@link #fPositions}. About syntax errors: this method is not a
   * validator, it is useful.
   */
  protected void foldPositions()
  {
    fPositions.clear();
    fSchemaPositions.clear();

    ITypedRegion[] partitions = null;
    try {
      if (this.fDocument instanceof IDocumentExtension3) {
        IDocumentExtension3 extension3 = (IDocumentExtension3) this.fDocument;
        partitions = extension3.computePartitioning(IZPartitions.Z_PARTITIONING,
            0, this.fDocument.getLength(), false);
      }
      else {
        partitions = this.fDocument.computePartitioning(0, this.fDocument
            .getLength());
      }
    } catch (BadLocationException ble) {
    } catch (BadPartitioningException bpe) {
    }

    try {
      for (int i = 0; i < partitions.length; i++) {
        ITypedRegion partition = partitions[i];
        int offset = partition.getOffset();
        int length = partition.getLength();
        if (IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF.equalsIgnoreCase(partition.getType())
            || IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH.equalsIgnoreCase(partition.getType())
            || IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA.equalsIgnoreCase(partition.getType())
            || IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF_OLD.equalsIgnoreCase(partition.getType())
            || IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH_OLD.equalsIgnoreCase(partition.getType())
            || IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA_OLD.equalsIgnoreCase(partition.getType())) {
          /*
           * The length of the position for a schema annotation is always 1. Then the drawing strategy
           * will use the editor document to access to the correcponding partition area.
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
        fPositions.add(new Position(offset, length));
      }
    } catch (BadLocationException e) {
    }

    Display.getDefault().asyncExec(new Runnable()
    {
      public void run()
      {
        if (fTextEditor instanceof ZEditor)
          ((ZEditor) fTextEditor).updateFoldingStructure(fPositions);
        if (fTextEditor instanceof ZEditor)
          ((ZEditor) fTextEditor).updateSchemaBoxAnnotations(fSchemaPositions);
      }
    });
  }
}
