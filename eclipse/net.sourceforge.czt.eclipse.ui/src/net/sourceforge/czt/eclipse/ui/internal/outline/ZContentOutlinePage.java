
package net.sourceforge.czt.eclipse.ui.internal.outline;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.CztImages;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.ui.internal.preferences.PreferenceConstants;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Spec;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPositionCategoryException;
import org.eclipse.jface.text.DefaultPositionUpdater;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IPositionUpdater;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

/**
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZContentOutlinePage extends ContentOutlinePage
    implements IDoubleClickListener
{
  
  private final static Visitor<List<? extends Term>> NODE_CHILDREN_VISITOR = 
      new NodeChildrenVisitor();
  
  private final ResourceManager resourceManager;
  private final Visitor<Image> termIconVisitor;
  
  /** A flag to show complete syntax tree in outline */
  private boolean showCompleteTree;
  
  /** A flag to show specification node in outline */
  private boolean showSpec;

  /**
   * The content provider for outline tree. It reacts to outline flags and rebuilds
   * the tree upon input change.
   */
  protected class OutlineContentProvider implements ITreeContentProvider
  {

    protected final static String SEGMENTS = "__z_segments"; //$NON-NLS-1$

    protected IPositionUpdater fPositionUpdater = new DefaultPositionUpdater(
        SEGMENTS);

    protected final List<CztTreeNode> fContents = new ArrayList<CztTreeNode>();

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

      if (newInput == null) {
        return;
      }
      
      IDocument document = fTextEditor.getDocumentProvider().getDocument(
          fTextEditor.getEditorInput());
      if (document == null) {
        return;
      }

      try {
        document.addPositionCategory(SEGMENTS);
        document.addPositionUpdater(fPositionUpdater);

        if (newInput instanceof ParsedData) {

          ParsedData data = (ParsedData) newInput;

          // build children tree
          CztTreeNodeFactory nodeFactory = new CztTreeNodeFactory(fTextEditor, data);
          List<CztTreeNode> topNodes = buildTree(nodeFactory, data);

          for (CztTreeNode node : topNodes) {
            if (node.getRange() != null) {
              document.addPosition(SEGMENTS, node.getRange());
            }
            
            fContents.add(node);
          }
        }
      }
      catch (BadPositionCategoryException x) {}
      catch (BadLocationException x) {}
    }

    public List<CztTreeNode> getContents()
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
      if (element instanceof CztTreeNode)
        return ((CztTreeNode) element).getChildren().size() > 0;
      return false;
    }

    /*
     * @see ITreeContentProvider#getParent(Object)
     */
    public Object getParent(Object element)
    {
      if (element instanceof CztTreeNode)
        return ((CztTreeNode) element).getParent();
      return null;
    }

    /*
     * @see ITreeContentProvider#getChildren(Object)
     */
    public Object[] getChildren(Object element)
    {
      if (element instanceof CztTreeNode)
        return ((CztTreeNode) element).getChildren().toArray();
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
      fContents.clear();
    }
    
    private List<? extends Term> getTermChildren(Term term)
    {
      if (showCompleteTree) {

        List<Term> childTerms = new ArrayList<Term>();
        for (Object child : term.getChildren()) {
          if (child instanceof Term) {
            childTerms.add((Term) child);
          }
        }
        
        return childTerms;
      }

      return term.accept(NODE_CHILDREN_VISITOR);
    }
    
    private List<CztTreeNode> buildTree(CztTreeNodeFactory nodeFactory, ParsedData data) {

      Spec spec = data.getSpec();
      if (spec == null) {
        return Collections.emptyList();
      }

      if (showSpec) {
        CztTreeNode specNode = nodeFactory.createTreeNode(spec);
        buildChildren(nodeFactory, spec, specNode);
        return Arrays.asList(specNode);
      }

      return buildChildren(nodeFactory, spec, null);
    }
    
    private List<CztTreeNode> buildChildren(CztTreeNodeFactory nodeFactory, Term term,
        CztTreeNode parentNode)
    {
      List<CztTreeNode> children = new ArrayList<CztTreeNode>();
      
      // use children either for complete tree or from a visitor
      for (Term child : getTermChildren((Term) term)) {
        
        // create child node and link with parent
        CztTreeNode childNode = nodeFactory.createTreeNode(child);
        
        childNode.setParent(parentNode);
        if (parentNode != null) {
          parentNode.addChild(childNode);
        }

        // mark for return
        children.add(childNode);
        
        // continue recursively into children
        buildChildren(nodeFactory, child, childNode);
      }

      return children;
    }
  }
  
  /**
   * The label provider displays text for nodes depending on whether the whole syntax
   * tree is shown, and of the current dialect.
   * @see TermLabelVisitorFactory
   */
  private class OutlineLabelProvider extends LabelProvider implements IColorProvider
  {

    @Override
    public String getText(Object element)
    {
      if (!(element instanceof CztTreeNode)) {
        return super.getText(element);
      }

      CztTreeNode node = (CztTreeNode) element;
      
      Visitor<String> textVisitor = 
          TermLabelVisitorFactory.getTermLabelVisitor(!showCompleteTree);
      return node.getTerm().accept(textVisitor);
    }
    
    @Override
    public Image getImage(Object element)
    {

      if (element instanceof CztTreeNode) {
        CztTreeNode node = (CztTreeNode) element;

        Image icon = node.getTerm().accept(termIconVisitor);
        if (icon != null) {
          return icon;
        }
      }

      // use default Z element icon
      return resourceManager.createImageWithDefault(CztImages.Z_ELEMENT);
      
//      // always use some icon - needed for overlays
//      return PlatformUI.getWorkbench().getSharedImages().getImage(
//          ISharedImages.IMG_OBJ_ELEMENT);
    }

    @Override
    public Color getForeground(Object element)
    {
      return null;
    }

    @Override
    public Color getBackground(Object element)
    {
      return null;
    }

  }
  
  protected Object fInput;

  protected String fContextMenuId;

  protected IZEditor fTextEditor;

  /**
   * Creates a content outline page using the given provider and the given
   * fEditor.
   * 
   * @param provider
   *            the document provider
   * @param fEditor
   *            the fEditor
   */
  public ZContentOutlinePage(String contextMenuId, IZEditor editor, ResourceManager resourceManager)
  {
    super();
    fContextMenuId = contextMenuId;
    fTextEditor = editor;
    this.resourceManager = resourceManager;
    termIconVisitor = new NodeIconVisitor(resourceManager);
  }
  
  private void registerToolbarActions(IActionBars actionBars)
  {
    IToolBarManager toolBarManager = actionBars.getToolBarManager();
    toolBarManager.add(new CompleteTreeAction());
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
    
    // register actions
    IActionBars actionBars = getSite().getActionBars();
    registerToolbarActions(actionBars);

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
    List<CztTreeNode> contents = contentProvider.getContents();
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
      if (element instanceof CztTreeNode) {
        Position pos = ((CztTreeNode) element).getRange();

        // if no position, still continue into children
        if (pos == null || ((pos.getOffset() <= offset)
            && (pos.getOffset() + pos.getLength() - 1 >= offset))) {
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
            autoExpand(viewer);
            control.setRedraw(true);
          }
        }
      });
    }
  }
  
  private void autoExpand(TreeViewer viewer) {
    
    int level = showCompleteTree ? 4 : 2;
    if (showSpec) {
      level++;
    }
    
    viewer.expandToLevel(level);
  }
  

  private class CompleteTreeAction extends Action
  {

    public CompleteTreeAction()
    {
      super("Show Complete Syntax Tree", SWT.TOGGLE);
      setToolTipText("Show Complete Syntax Tree");

      // setDescription("?");
      setImageDescriptor(CztImages.COMPLETE_TREE);

      IPreferenceStore preferenceStore = CztUIPlugin.getDefault().getPreferenceStore();
      boolean showCompleteTree = preferenceStore
          .getBoolean(PreferenceConstants.OUTLINE_Z_COMPLETE_TREE);
      setShowCompleteTree(showCompleteTree);
    }

    /*
     * @see org.eclipse.jface.action.Action#run()
     */
    public void run()
    {
      setShowCompleteTree(!showCompleteTree);
      update();
    }

    private void setShowCompleteTree(boolean show)
    {
      showCompleteTree = show;
      setChecked(show);
//      getTreeViewer().refresh(false);

      IPreferenceStore preferenceStore = CztUIPlugin.getDefault().getPreferenceStore();
      preferenceStore.setValue(PreferenceConstants.OUTLINE_Z_COMPLETE_TREE, show);
    }
  }
}
