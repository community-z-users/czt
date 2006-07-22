
package net.sourceforge.czt.eclipse.outline;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPositionCategoryException;
import org.eclipse.jface.text.DefaultPositionUpdater;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IPositionUpdater;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

/**
 * @author Chengdong Xu
 */
public class ZContentOutlinePage extends ContentOutlinePage
    implements
      IDoubleClickListener
{

  /**
   * 
   */
  protected class OutlineContentProvider implements ITreeContentProvider
  {

    protected final static String SEGMENTS = "__z_segments"; //$NON-NLS-1$

    protected IPositionUpdater fPositionUpdater = new DefaultPositionUpdater(
        SEGMENTS);

    protected List<CztSegment> fContents = new ArrayList<CztSegment>();

    /*
     * @see IContentProvider#inputChanged(Viewer, Object, Object)
     */
    public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
    {
      if (oldInput != null) {
        IDocument document = fTextEditor.getDocumentProvider().getDocument(
            fTextEditor.getEditorInput());
        if (document != null) {
          try {
            document.removePositionCategory(SEGMENTS);
          } catch (BadPositionCategoryException x) {
          }
          document.removePositionUpdater(fPositionUpdater);
        }
      }

      fContents.clear();

      if (newInput != null) {
        IDocument document = fTextEditor.getDocumentProvider().getDocument(
            fTextEditor.getEditorInput());
        if (document != null) {
          try {
            document.addPositionCategory(SEGMENTS);
            document.addPositionUpdater(fPositionUpdater);

            if (newInput instanceof CztSegment) {
              for (CztSegment child : ((CztSegment) newInput).getChildren()) {
                if (child.getRange() != null) {
                  document.addPosition(SEGMENTS, child.getRange());
                  fContents.add(child);
                }
              }
            }
          } catch (BadPositionCategoryException x) {
          } catch (BadLocationException x) {
          }
        }
      }
    }

    public List<CztSegment> getContents()
    {
      return this.fContents;
    }

    /*
     * @see IStructuredContentProvider#getElements(Object)
     */
    public Object[] getElements(Object element)
    {
      return fContents.toArray();
    }

    /*
     * @see ITreeContentProvider#hasChildren(Object)
     */
    public boolean hasChildren(Object element)
    {
      if (element instanceof CztSegment)
        return ((CztSegment) element).getChildren().size() > 0;
      return false;
    }

    /*
     * @see ITreeContentProvider#getParent(Object)
     */
    public Object getParent(Object element)
    {
      if (element instanceof CztSegment)
        return ((CztSegment) element).getParent();
      return null;
    }

    /*
     * @see ITreeContentProvider#getChildren(Object)
     */
    public Object[] getChildren(Object element)
    {
      if (element instanceof CztSegment)
        return ((CztSegment) element).getChildren().toArray();
      return new Object[0];
    }

    /*
     * @see IContentProvider#isDeleted(Object)
     */
    public boolean isDeleted(Object element)
    {
      return false;
    }

    /*
     * @see IContentProvider#dispose
     */
    public void dispose()
    {
      if (fContents != null) {
        fContents.clear();
        fContents = null;
      }
    }
  }

  protected Object fInput;

  protected String fContextMenuId;

  protected ITextEditor fTextEditor;

  /**
   * Creates a content outline page using the given provider and the given
   * editor.
   * 
   * @param provider
   *            the document provider
   * @param editor
   *            the editor
   */
  public ZContentOutlinePage(String contextMenuId, ITextEditor editor)
  {
    super();
    fContextMenuId = contextMenuId;
    fTextEditor = editor;
  }

  /*
   * (non-Javadoc) Method declared on ContentOutlinePage
   */
  public void createControl(Composite parent)
  {

    super.createControl(parent);

    TreeViewer viewer = getTreeViewer();
    viewer.setContentProvider(new OutlineContentProvider());
    viewer.setLabelProvider(new DecoratingCztLabelProvider(
        new OutlineLabelProvider()));
    viewer.addSelectionChangedListener(this);
    viewer.addDoubleClickListener(this);

    if (fInput != null)
      viewer.setInput(fInput);
  }

  /**
   * 
   */
  public void doubleClick(DoubleClickEvent event)
  {
    ISelection selection = event.getSelection();
    if (selection.isEmpty())
      fTextEditor.resetHighlightRange();
    else {
      TreeViewer viewer = getTreeViewer();
      Object select = ((IStructuredSelection) selection).getFirstElement();
      if (viewer.isExpandable(select))
        viewer.setExpandedState(select, !viewer.getExpandedState(select));
    }
  }

  public void select(int offset)
  {
    if (offset < 0) {
      this.setSelection(null);
      return;
    }

    OutlineContentProvider contentProvider = (OutlineContentProvider) this
        .getTreeViewer().getContentProvider();
    List<CztSegment> contents = contentProvider.getContents();
    Object element = getNodeOfPoint(contentProvider, contents.toArray(), offset);
    if (element == null) {
      this.getTreeViewer().setSelection(null);
    }
    else {
      IStructuredSelection selection = new StructuredSelection(element);
      this.getTreeViewer().setSelection(selection, false);
    }
  }

  public Object getNodeOfPoint(OutlineContentProvider contentProvider,
      Object[] elements, int offset)
  {
    Object node = null;
    for (Object element : elements) {
      if (element instanceof CztSegment) {
        Position pos = ((CztSegment) element).getRange();
        if ((pos.getOffset() <= offset)
            && (pos.getOffset() + pos.getLength() - 1 >= offset)) {
          node = element;
          Object childNode = getNodeOfPoint(contentProvider, contentProvider
              .getChildren(element), offset);
          if (childNode != null)
            node = childNode;
          break;
        }
      }
    }
    return node;
  }

  /*
   * (non-Javadoc) Method declared on ContentOutlinePage
   */
  public void selectionChanged(SelectionChangedEvent event)
  {
    super.selectionChanged(event);
  }

  /**
   * Sets the input of the outline page
   * 
   * @param input - the input of this outline page
   */
  public void setInput(Object input)
  {
    fInput = input;
    update();
  }

  /**
   * Updates the outline page.
   */
  public void update()
  {
    final TreeViewer viewer = getTreeViewer();

    if (viewer != null) {
      Display.getDefault().asyncExec(new Runnable()
      {
        public void run()
        {
          Control control = viewer.getControl();
          if (control != null && !control.isDisposed()) {
            control.setRedraw(false);
            viewer.setInput(fInput);
            viewer.expandAll();
            control.setRedraw(true);
          }
        }
      });
    }
  }
}
