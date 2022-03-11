
package net.sourceforge.czt.eclipse.ui.views;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.CztImages;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.internal.editors.FontUpdater;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.preferences.SimpleZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.ui.internal.util.IColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.PartAdapter;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.session.Markup;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.GroupMarker;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.commands.ActionHandler;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchCommandConstants;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.AnnotationPreference;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.eclipse.ui.texteditor.DefaultMarkerAnnotationAccess;
import org.eclipse.ui.texteditor.MarkerAnnotationPreferences;
import org.eclipse.ui.texteditor.SourceViewerDecorationSupport;

/**
 * Adapted from org.eclipse.jdt.internal.ui.infoviews.AbstractInfoView
 * 
 * @author Andrius Velykis
 */
public class ZInfoView extends ViewPart implements ISelectionListener
{

  protected static final String TOOLBAR_GROUP_INFO_VIEW = "info-view";

  private static final String VIEW_ID = CztUIPlugin.PLUGIN_ID + ".views.ZInfo";

  private static final String PROP_FORCE_UNICODE = VIEW_ID + ".forceUnicode";

  static {
    IPreferenceStore preferenceStore = CztUIPlugin.getDefault().getPreferenceStore();
    preferenceStore.setDefault(PROP_FORCE_UNICODE, false);
  }

  private Composite main;

  private ZSourceViewer zViewer;

  private FontUpdater fontUpdater;

  /** The text context menu to be disposed. */
  private Menu fTextContextMenu;

  /**
     * True if linking with selection is enabled, false otherwise.
     */
  private boolean linking = true;

  /**
   * Action to enable and disable link with selection.
   */
  private LinkAction toggleLinkAction;

  private boolean forceUnicode;

  /**
   * The last selected element if linking was disabled.
   */
  private IZInfoObject lastSelection;

  /** The current input. */
  private IZInfoObject currentViewInput;

  /**
   * The compute job reference used to cancel it when starting a new one
   */
  private Job computeJob;

  /*
   * @see IPartListener2
   */
  private IPartListener2 partListener = new PartAdapter()
  {

    @Override
    public void partVisible(IWorkbenchPartReference ref)
    {
      if (ref.getId().equals(getSite().getId())) {
        IWorkbenchPart activePart = ref.getPage().getActivePart();
        if (activePart != null) {
          selectionChanged(activePart, ref.getPage().getSelection());
        }
        startListeningForSelectionChanges();
      }
    }

    @Override
    public void partHidden(IWorkbenchPartReference ref)
    {
      if (ref.getId().equals(getSite().getId()))
        stopListeningForSelectionChanges();
    }

    @Override
    public void partInputChanged(IWorkbenchPartReference ref)
    {
      if (!ref.getId().equals(getSite().getId()))
        computeAndSetInput(ref.getPart(false));
    }
  };

  @Override
  public void createPartControl(Composite parent)
  {

    main = new Composite(parent, SWT.NONE);
    main.setLayout(GridLayoutFactory.fillDefaults().create());

    Control viewerControl = createZViewer(main);
    viewerControl.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());

    createActions();
    fillActionBars(getViewSite().getActionBars());

    getSite().getWorkbenchWindow().getPartService().addPartListener(partListener);
  }

  /**
   * Copied from net.sourceforge.czt.eclipse.ui.views.ZConversionView
   * @param parent
   */
  private Control createZViewer(Composite parent)
  {

    IPreferenceStore store = new ChainedPreferenceStore(new IPreferenceStore[]{
        CztUIPlugin.getDefault().getPreferenceStore(), EditorsUI.getPreferenceStore()});
    IColorManager colorManager = CztUIPlugin.getDefault().getCZTTextTools().getColorManager();

    zViewer = new ZSourceViewer(parent, null, null, true, SWT.V_SCROLL | SWT.H_SCROLL, store);

    
    // init decoration support - it is necessary to display annotations
    // Note: decoration support must be before configuration
    SourceViewerDecorationSupport decorationSupport = new SourceViewerDecorationSupport(
        zViewer, null, new DefaultMarkerAnnotationAccess(), colorManager);
    
    for (Object pref : new MarkerAnnotationPreferences().getAnnotationPreferences()) {
      decorationSupport.setAnnotationPreference((AnnotationPreference) pref);
    }
    decorationSupport.install(store);
    
    // now configure the viewer
    ZSourceViewerConfiguration configuration = new SimpleZSourceViewerConfiguration(
        colorManager, store, null, IZPartitions.Z_PARTITIONING, true);
    zViewer.configure(configuration);
    fontUpdater = FontUpdater.enableFor(zViewer, configuration, store, JFaceResources.TEXT_FONT);
    
    zViewer.setEditable(false);
    zViewer.setDocument(new Document());

    // setup context menu
    MenuManager manager = new MenuManager();
    manager.setRemoveAllWhenShown(true);
    manager.addMenuListener(new IMenuListener()
    {
      @Override
      public void menuAboutToShow(IMenuManager menu)
      {
        setFocus();
        contextMenuAboutToShow(menu);
      }
    });

    Control textWidget = zViewer.getTextWidget();
    fTextContextMenu = manager.createContextMenu(textWidget);
    textWidget.setMenu(fTextContextMenu);

    getSite().registerContextMenu(manager, zViewer);
    // Make the selection available
    getSite().setSelectionProvider(zViewer);

    return zViewer.getControl();
  }

  protected void contextMenuAboutToShow(IMenuManager menu)
  {
  }

  protected void setContents(Object input, Markup markup)
  {
    
    String text = input != null ? String.valueOf(input) : "";

    Document document = new Document(text);

    String fileType = ZEditorUtil.getFileType(markup);
    CztUIPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
        document, IZPartitions.Z_PARTITIONING, fileType);

    fontUpdater.setFont(ZEditorUtil.getEditorFont(markup));
    zViewer.setDocument(document);
  }

  /**
   * Creates the actions and action groups for this view.
   */
  private void createActions()
  {
    toggleLinkAction = new LinkAction();
    toggleLinkAction.setActionDefinitionId(
        IWorkbenchCommandConstants.NAVIGATE_TOGGLE_LINK_WITH_EDITOR);
  }

  /**
   * Fills the actions bars.
   * <p>
   * @param actionBars the action bars
   */
  private void fillActionBars(IActionBars actionBars)
  {
    IToolBarManager toolBar = actionBars.getToolBarManager();
    fillToolBar(toolBar);

    IHandlerService handlerService = (IHandlerService) getSite().getService(IHandlerService.class);
    handlerService.activateHandler(
        IWorkbenchCommandConstants.NAVIGATE_TOGGLE_LINK_WITH_EDITOR,
        new ActionHandler(toggleLinkAction));
  }

  /**
   * Fills the tool bar.
   * <p>
   *
   * @param tbm the tool bar manager
   */
  protected void fillToolBar(IToolBarManager tbm)
  {

    tbm.add(new Separator(TOOLBAR_GROUP_INFO_VIEW));

    tbm.add(new ForceUnicodeAction());

    tbm.add(new GroupMarker("view"));
    tbm.add(toggleLinkAction);
  }

  @Override
  public void dispose()
  {
    getSite().getWorkbenchWindow().getPartService().removePartListener(partListener);

    if (fTextContextMenu != null) {
      fTextContextMenu.dispose();
      fTextContextMenu = null;
    }

    super.dispose();
  }

  @Override
  public void setFocus()
  {
    zViewer.getControl().setFocus();
  }

  /**
   * Start to listen for selection changes.
   */
  private void startListeningForSelectionChanges()
  {
    getSite().getPage().addPostSelectionListener(this);
  }

  /**
   * Stop to listen for selection changes.
   */
  private void stopListeningForSelectionChanges()
  {
    getSite().getPage().removePostSelectionListener(this);
  }

  /**
   * Sets whether this info view reacts to selection
   * changes in the workbench.
   *
   * @param enabled if true then the input is set on selection changes
   */
  private void setLinkingEnabled(boolean enabled)
  {
    linking = enabled;

    if (linking && lastSelection != null) {
      setInput(lastSelection);
    }
  }

  /**
   * Returns whether this info view reacts to selection
   * changes in the workbench.
   *
   * @return true if linking with selection is enabled
   */
  private boolean isLinkingEnabled()
  {
    return linking;
  }

  /*
   * @see ISelectionListener#selectionChanged(org.eclipse.ui.IWorkbenchPart, org.eclipse.jface.viewers.ISelection)
   */
  @Override
  public void selectionChanged(IWorkbenchPart part, ISelection selection)
  {
    if (part.equals(this)) {
      return;
    }

    if (!linking) {
      IZInfoObject zElement = findSelectedZInfoElement(part, selection, getCaretPosition(part));
      if (zElement != null) {
        lastSelection = zElement;
      }
    }
    else {
      lastSelection = null;
      computeAndSetInput(part);
    }
  }

  /**
   * Tells whether the new input should be ignored if the current input is the same.
   *
   * @param ze the new input, may be <code>null</code>
   * @param part the workbench part
   * @param selection the current selection from the part that provides the input
   * @return <code>true</code> if the new input should be ignored
   */
  protected boolean isIgnoringNewInput(IZInfoObject ze, IWorkbenchPart part, ISelection selection)
  {
    return currentViewInput != null && currentViewInput.equals(ze) && ze != null;
  }

  /**
   * Finds and returns the Z/EVES element selected in the given part.
   *
   * @param part the workbench part for which to find the selected Z/EVES element
   * @param selection the selection
   * @return the selected Java element
   */
  protected IZInfoObject findSelectedZInfoElement(IWorkbenchPart part, ISelection selection,
      int caretPos)
  {

    if (selection instanceof IStructuredSelection) {
      Object element = ((IStructuredSelection) selection).getFirstElement();
      return findZInfoElement(element);
    }

    return null;
  }

  /**
   * Tries to get a Z info element out of the given element.
   *
   * @param element an object
   * @return the Z info element represented by the given element or <code>null</code>
   */
  private IZInfoObject findZInfoElement(Object element)
  {

    if (element == null) {
      return null;
    }

    IZInfoObject ze = null;

    if (element instanceof IZInfoObject) {
      ze = (IZInfoObject) element;
    }

    if (element instanceof IAdaptable) {
      ze = (IZInfoObject) ((IAdaptable) element).getAdapter(IZInfoObject.class);
    }

    return ze;
  }

  /**
   * Determines all necessary details and delegates the computation into
   * a background job.
   *
   * @param part the workbench part
   */
  private void computeAndSetInput(final IWorkbenchPart part)
  {
    computeAndDoSetInput(part, null);
  }

  /**
   * Sets the input for this view.
   *
   * @param element the Z info element
   */
  private final void setInput(final IZInfoObject element)
  {
    computeAndDoSetInput(null, element);
  }

  /**
   * Determines all necessary details and delegates the computation into
   * a background thread. One of part or element must be non-null.
   *
   * @param part the workbench part, or <code>null</code> if <code>element</code> not <code>null</code>
   * @param element the Z/EVES element, or <code>null</code> if <code>part</code> not <code>null</code>
   */
  private void computeAndDoSetInput(final IWorkbenchPart part, final IZInfoObject element)
  {
    Assert.isLegal(part != null || element != null);

    final ISelection selection;
    if (element != null) {
      selection = null;
    }
    else {
      ISelectionProvider provider = part.getSite().getSelectionProvider();
      if (provider == null) {
        return;
      }

      selection = provider.getSelection();
      if (!isSelectionInteresting(part, selection)) {
        return;
      }
    }

    // caret is necessary if we want to show info of things in the editor
    final int caretPos = getCaretPosition(part);

    if (computeJob != null) {
      computeJob.cancel();
    }

    computeJob = new Job("Loading Z element information")
    {

      @Override
      protected IStatus run(IProgressMonitor monitor)
      {
        if (monitor.isCanceled()) {
          return Status.CANCEL_STATUS;
        }

        final IZInfoObject ze;
        if (element != null) {
          ze = element;
        }
        else {
          ze = findSelectedZInfoElement(part, selection, caretPos);
          if (isIgnoringNewInput(ze, part, selection)) {
            return Status.OK_STATUS;
          }
        }

        if (monitor.isCanceled()) {
          return Status.CANCEL_STATUS;
        }

        // The actual computation
        final Object input = loadContents(part, selection, ze, monitor);
        if (input == null) {
          return Status.OK_STATUS;
        }

        if (monitor.isCanceled()) {
          return Status.CANCEL_STATUS;
        }

        final String description = loadDescription(part, selection, ze, monitor);

        if (monitor.isCanceled()) {
          return Status.CANCEL_STATUS;
        }
        
        final Job theJob = this;
        PlatformUtil.runInUI(new Runnable()
        {
          @Override
          public void run()
          {

            if (computeJob != theJob || getViewSite().getShell().isDisposed()) {
              return;
            }

            doSetInput(ze, input, description);
          }
        });

        return Status.OK_STATUS;
      }
    };

    computeJob.setPriority(Job.SHORT);
    computeJob.schedule();
  }

  /**
   * Computes the input for this view based on the given elements
   *
   * @param part the part that triggered the current element update, or <code>null</code>
   * @param selection the new selection, or <code>null</code>
   * @param element the new Z element that will be displayed
   * @param monitor a progress monitor
   * @return the input or <code>null</code> if the input was not computed successfully
   */
  protected Object loadContents(IWorkbenchPart part, ISelection selection, IZInfoObject element,
      IProgressMonitor monitor)
  {

    if (element == null) {
      return null;
    }

    try {
      return element.loadContents(getElementMarkup(element), monitor);
    }
    catch (CoreException e) {
      CztUIPlugin.log(e);
    }

    return null;
  }

  /**
   * Computes the contents description that will be displayed for the current element.
   *
   * @param part the part that triggered the current element update, or <code>null</code>
   * @param selection the new selection, or <code>null</code>
   * @param inputElement the new java element that will be displayed
   * @param monitor a progress monitor
   * @return the contents description for the provided <code>inputElement</code>
   */
  protected String loadDescription(IWorkbenchPart part, ISelection selection,
      IZInfoObject inputElement, IProgressMonitor monitor)
  {

    if (inputElement == null) {
      return null;
    }

    try {
      return inputElement.loadDescription(monitor);
    }
    catch (CoreException e) {
      CztUIPlugin.log(e);
    }

    return null;
  }

  protected void doSetInput(IZInfoObject element, Object input, String description)
  {

    this.currentViewInput = element;
    String descText = description != null ? description : "";

    setContents(input, getElementMarkup(element));

    setContentDescription(descText);
    setTitleToolTip(descText);
  }

  protected Markup getElementMarkup(IZInfoObject element)
  {
    return (forceUnicode || element == null) ? Markup.UNICODE : element.getMarkup();
  }
  
  protected ISourceViewer getViewer()
  {
    return zViewer;
  }

  protected boolean isSelectionInteresting(IWorkbenchPart part, ISelection selection)
  {

    if (selection == null) {
      return false;
    }

    return !selection.isEmpty();
  }

  private int getCaretPosition(IWorkbenchPart part)
  {
    if (part instanceof IZEditor) {
      return ZEditorUtil.getCaretPosition((ZEditor) part);
    }

    return -1;
  }

  public IZInfoObject getCurrentInput()
  {
    return currentViewInput;
  }

  protected void reload()
  {
    if (currentViewInput != null) {
      setInput(currentViewInput);
    }
  }
  
  protected void setMarkup(Markup markup) {
    fontUpdater.setFont(ZEditorUtil.getEditorFont(markup));
  }


  /**
   * Action to toggle linking with selection.
   */
  private class LinkAction extends Action
  {

    public LinkAction()
    {
      super("Link with Selection", SWT.TOGGLE);
      setToolTipText("Link with Selection");

      ISharedImages images = PlatformUI.getWorkbench().getSharedImages();
      setImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_ELCL_SYNCED));
      setDisabledImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_ELCL_SYNCED_DISABLED));
      setChecked(isLinkingEnabled());
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.jface.action.Action#run()
     */
    @Override
    public void run()
    {
      setLinkingEnabled(!isLinkingEnabled());
    }
  }


  private class ForceUnicodeAction extends Action
  {

    public ForceUnicodeAction()
    {
      super("Force Unicode", SWT.TOGGLE);
      setToolTipText("Force Unicode");

      // setDescription("?");
      setImageDescriptor(CztImages.UNICODE);

      IPreferenceStore preferenceStore = CztUIPlugin.getDefault().getPreferenceStore();
      boolean forceUnicode = preferenceStore.getBoolean(PROP_FORCE_UNICODE);
      setForceUnicode(forceUnicode);
    }

    /*
     * @see org.eclipse.jface.action.Action#run()
     */
    @Override
    public void run()
    {
      setForceUnicode(!forceUnicode);

      reload();
    }

    private void setForceUnicode(boolean force)
    {
      forceUnicode = force;
      setChecked(force);

      IPreferenceStore preferenceStore = CztUIPlugin.getDefault().getPreferenceStore();
      preferenceStore.setValue(PROP_FORCE_UNICODE, force);
    }
  }

}
