package net.sourceforge.czt.eclipse.zeves.views;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.IZPartitions;
import net.sourceforge.czt.eclipse.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.preferences.PreferenceConstants;
import net.sourceforge.czt.eclipse.preferences.SimpleZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.preferences.ZSourcePreviewerUpdater;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.eclipse.zeves.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorUtil;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.commands.ActionHandler;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
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
import org.eclipse.ui.texteditor.ChainedPreferenceStore;

/**
 * Adapted from org.eclipse.jdt.internal.ui.infoviews.AbstractInfoView
 * 
 * @author Andrius Velykis
 */
public class ZEvesOutputView extends ViewPart implements ISelectionListener {

	private static final String PROP_FORCE_UNICODE = ZEvesPlugin.PLUGIN_ID + ".output.forceUnicode";
	
	static {
		IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
		preferenceStore.setDefault(PROP_FORCE_UNICODE, false);
	}
	
	private ZSourceViewer zViewer;
//	
//	private Text zViewer;
	
	/**
     * True if linking with selection is enabled, false otherwise.
     */
    private boolean linking= true;
    
    /**
     * Action to enable and disable link with selection.
     */
    private LinkAction toggleLinkAction;
    
    private boolean forceUnicode;

    /**
     * The last selected element if linking was disabled.
     */
    private IZEvesElement lastSelection;
    
    /** The current input. */
    protected IZEvesElement currentViewInput;

    /** Counts the number of background computation requests. */
    private volatile int globalComputeCount;

    /**
     * Progress monitor used to cancel pending computations.
     */
    private IProgressMonitor fComputeProgressMonitor;
    
    /*
     * @see IPartListener2
     */
	private IPartListener2 partListener = new IPartListener2() {
		
		public void partVisible(IWorkbenchPartReference ref) {
			if (ref.getId().equals(getSite().getId())) {
				IWorkbenchPart activePart = ref.getPage().getActivePart();
				if (activePart != null) {
					selectionChanged(activePart, ref.getPage().getSelection());
				}
				startListeningForSelectionChanges();
			}
		}

		public void partHidden(IWorkbenchPartReference ref) {
			if (ref.getId().equals(getSite().getId()))
				stopListeningForSelectionChanges();
		}

		public void partInputChanged(IWorkbenchPartReference ref) {
			if (!ref.getId().equals(getSite().getId()))
				computeAndSetInput(ref.getPart(false));
		}

		public void partActivated(IWorkbenchPartReference ref) {
		}

		public void partBroughtToTop(IWorkbenchPartReference ref) {
		}

		public void partClosed(IWorkbenchPartReference ref) {
		}

		public void partDeactivated(IWorkbenchPartReference ref) {
		}

		public void partOpened(IWorkbenchPartReference ref) {
		}
	};
	
	@Override
	public void createPartControl(Composite parent) {
		
//		zViewer = new ZSourceViewer(parent, verticalRuler, overviewRuler, showsAnnotationOverview, styles, store);
		
//		zViewer = new Text(parent, SWT.MULTI | SWT.V_SCROLL | SWT.WRAP);
//		zViewer.setEditable(false);
		createZViewer(parent);
		
		createActions();
		fillActionBars(getViewSite().getActionBars());
		
		getSite().getWorkbenchWindow().getPartService().addPartListener(partListener);
	}
	
	/**
	 * Copied from net.sourceforge.czt.eclipse.views.ZConversionView
	 * @param parent
	 */
	private void createZViewer(Composite parent) {
		
		IPreferenceStore generalTextStore = EditorsUI.getPreferenceStore();
		IPreferenceStore store = new ChainedPreferenceStore(new IPreferenceStore[] {
				CZTPlugin.getDefault().getPreferenceStore(), generalTextStore });

		zViewer = new ZSourceViewer(parent, null, null, false, SWT.V_SCROLL | SWT.H_SCROLL, store);

		SimpleZSourceViewerConfiguration configuration = new SimpleZSourceViewerConfiguration(CZTPlugin.getDefault()
				.getCZTTextTools().getColorManager(), store, null, IZPartitions.Z_PARTITIONING, false);
		zViewer.configure(configuration);
		Font font = JFaceResources.getFont(PreferenceConstants.EDITOR_TEXT_FONT);
		zViewer.getTextWidget().setFont(font);
		new ZSourcePreviewerUpdater(zViewer, configuration, store);
		FontData fontData = new FontData("CZT", 12, SWT.NORMAL);
		zViewer.getTextWidget().setFont(new Font(Display.getDefault(), fontData));
		zViewer.setEditable(false);
		zViewer.setDocument(new Document());
	}
	
	private void setText(String text) {
		
	    Document document = new Document(text);
	    
		CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
				document, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
	    
	    zViewer.setDocument(document);
	}
	
    /**
     * Creates the actions and action groups for this view.
     */
    private void createActions() {
        toggleLinkAction= new LinkAction();
        toggleLinkAction.setActionDefinitionId(IWorkbenchCommandConstants.NAVIGATE_TOGGLE_LINK_WITH_EDITOR);
    }
    
    /**
     * Fills the actions bars.
     * <p>
     * @param actionBars the action bars
     */
    private void fillActionBars(IActionBars actionBars) {
        IToolBarManager toolBar= actionBars.getToolBarManager();
        fillToolBar(toolBar);

        IHandlerService handlerService= (IHandlerService) getSite().getService(IHandlerService.class);
        handlerService.activateHandler(IWorkbenchCommandConstants.NAVIGATE_TOGGLE_LINK_WITH_EDITOR, new ActionHandler(toggleLinkAction));

//		IAction action = getSelectAllAction();
//		if (action != null) {
//			actionBars.setGlobalActionHandler(ActionFactory.SELECT_ALL.getId(), action);
//		}
    }
    
    /**
     * Fills the tool bar.
     * <p>
     *
     * @param tbm the tool bar manager
     */
    protected void fillToolBar(IToolBarManager tbm) {
    	
    	tbm.add(new Separator("view"));
    	
    	tbm.add(new ForceUnicodeAction());
    	tbm.add(toggleLinkAction);
    }


	@Override
	public void dispose() {
		getSite().getWorkbenchWindow().getPartService().removePartListener(partListener);
		
		super.dispose();
	}

	@Override
	public void setFocus() {
		zViewer.getControl().setFocus();
	}
	
	/**
	 * Start to listen for selection changes.
	 */
	private void startListeningForSelectionChanges() {
		getSite().getPage().addPostSelectionListener(this);
	}

	/**
	 * Stop to listen for selection changes.
	 */
	private void stopListeningForSelectionChanges() {
		getSite().getPage().removePostSelectionListener(this);
	}
	
    /**
     * Sets whether this info view reacts to selection
     * changes in the workbench.
     *
     * @param enabled if true then the input is set on selection changes
     */
	private void setLinkingEnabled(boolean enabled) {
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
	private boolean isLinkingEnabled() {
		return linking;
	}
	
    /*
     * @see ISelectionListener#selectionChanged(org.eclipse.ui.IWorkbenchPart, org.eclipse.jface.viewers.ISelection)
     */
	public void selectionChanged(IWorkbenchPart part, ISelection selection) {
		if (part.equals(this)) {
			return;
		}

		if (!linking) {
			IZEvesElement zElement = findSelectedZEvesElement(part, selection, getCaretPosition(part));
			if (zElement != null) {
				lastSelection = zElement;
			}
		} else {
			lastSelection = null;
			computeAndSetInput(part);
		}
	}
    
    /**
     * Tells whether the new input should be ignored
     * if the current input is the same.
     *
     * @param je the new input, may be <code>null</code>
     * @param part the workbench part
     * @param selection the current selection from the part that provides the input
     * @return <code>true</code> if the new input should be ignored
     */
	protected boolean isIgnoringNewInput(IZEvesElement je, IWorkbenchPart part, ISelection selection) {
		return currentViewInput != null && currentViewInput.equals(je) && je != null;
	}

    /**
     * Finds and returns the Z/Eves element selected in the given part.
     *
     * @param part the workbench part for which to find the selected Z/Eves element
     * @param selection the selection
     * @return the selected Java element
     */
	protected IZEvesElement findSelectedZEvesElement(IWorkbenchPart part, ISelection selection, int caretPos) {
		
		// in the future - resolve from ZEditor if needed?
		if (part instanceof ZEditor && selection instanceof ITextSelection) {
			return ZEditorResults.getZEvesResult((ZEditor) part, (ITextSelection) selection, caretPos);
		} 
		
		if (selection instanceof IStructuredSelection) {
			Object element = ((IStructuredSelection) selection).getFirstElement();
			return findZEvesElement(element);
		}
		
		return null;
	}

    /**
     * Tries to get a Z/Eves element out of the given element.
     *
     * @param element an object
     * @return the Z/Eves element represented by the given element or <code>null</code>
     */
	private IZEvesElement findZEvesElement(Object element) {

		if (element == null) {
			return null;
		}

		IZEvesElement ze = null;
		
		if (element instanceof IZEvesElement) {
			ze = (IZEvesElement) element;
		}
		
//		if (element instanceof IAdaptable) {
//			ze = (IZEvesElement) ((IAdaptable) element).getAdapter(IZEvesElement.class);
//		}

		return ze;
	}
    
    /**
     * Determines all necessary details and delegates the computation into
     * a background thread.
     *
     * @param part the workbench part
     */
	private void computeAndSetInput(final IWorkbenchPart part) {
		computeAndDoSetInput(part, null);
	}

    /**
     * Sets the input for this view.
     *
     * @param element the Z/Eves element
     */
	private final void setInput(final IZEvesElement element) {
		computeAndDoSetInput(null, element);
	}
    
    /**
     * Determines all necessary details and delegates the computation into
     * a background thread. One of part or element must be non-null.
     *
     * @param part the workbench part, or <code>null</code> if <code>element</code> not <code>null</code>
     * @param element the Z/Eves element, or <code>null</code> if <code>part</code> not <code>null</code>
     */
    private void computeAndDoSetInput(final IWorkbenchPart part, final IZEvesElement element) {
		Assert.isLegal(part != null || element != null);

		final int currentCount = ++globalComputeCount;

		final ISelection selection;
		if (element != null) {
			selection = null;
		} else {
			ISelectionProvider provider = part.getSite().getSelectionProvider();
			if (provider == null) {
				return;
			}

			selection = provider.getSelection();
			if (!isSelectionInteresting(part, selection)) {
				return;
			}
//			if (selection == null || selection.isEmpty()) {
//				return;
//			}
		}
		
		final int caretPos = getCaretPosition(part);

		if (fComputeProgressMonitor != null) {
			fComputeProgressMonitor.setCanceled(true);
		}

		final IProgressMonitor computeProgressMonitor = new NullProgressMonitor();
		fComputeProgressMonitor = computeProgressMonitor;

		Thread thread = new Thread("Z/Eves info view input computer") { //$NON-NLS-1$
			@Override
			public void run() {
				if (currentCount != globalComputeCount) {
					return;
				}

				if (computeProgressMonitor.isCanceled()) {
					return;
				}
				
				final IZEvesElement ze;
				if (element != null) {
					ze = element;
				} else {
					ze = findSelectedZEvesElement(part, selection, caretPos);
					if (isIgnoringNewInput(ze, part, selection)) {
						return;
					}
				}
				
				if (computeProgressMonitor.isCanceled()) {
					return;
				}

				// The actual computation
				final Object input = computeInput(part, selection, ze, computeProgressMonitor);
				if (input == null) {
					return;
				}
				
				if (computeProgressMonitor.isCanceled()) {
					return;
				}

				final String description = computeDescription(part, selection, ze, computeProgressMonitor);

				if (computeProgressMonitor.isCanceled()) {
					return;
				}
				
				Shell shell = getSite().getShell();
				if (shell.isDisposed()) {
					return;
				}

				Display display = shell.getDisplay();
				if (display.isDisposed()) {
					return;
				}

				display.asyncExec(new Runnable() {
					/*
					 * @see java.lang.Runnable#run()
					 */
					public void run() {

						if (globalComputeCount != currentCount || getViewSite().getShell().isDisposed()) {
							return;
						}

						currentViewInput = ze;
						doSetInput(input, description);

						fComputeProgressMonitor = null;
					}
				});
			}
		};

		if (!ZEvesPlugin.getZEves().isRunning()) {
			// Z/Eves not running, ignore updates
			setContentDescription("Z/Eves is not running");
			setTitleToolTip(null);
			return;
		}
		
		setContentDescription("");

		thread.setDaemon(true);
		thread.setPriority(Thread.MIN_PRIORITY);
		thread.start();
    }
    
    /**
     * Computes the input for this view based on the given elements
     *
     * @param part the part that triggered the current element update, or <code>null</code>
     * @param selection the new selection, or <code>null</code>
     * @param element the new java element that will be displayed
     * @param monitor a progress monitor
     * @return the input or <code>null</code> if the input was not computed successfully
     * @since 3.4
     */
	private Object computeInput(IWorkbenchPart part, ISelection selection, IZEvesElement element, IProgressMonitor monitor) {
		return computeInput(element);
	}
	
	private Object computeInput(IZEvesElement element) {
		
		if (element == null) {
			return null;
		}
		
		ZEvesApi api = ZEvesPlugin.getZEves().getApi();
		Markup markup = forceUnicode ? Markup.UNICODE : null;
		
		try {
			return element.loadContents(api, markup);
		} catch (ZEvesException e) {
			ZEvesPlugin.getDefault().log("Problems loading Z/Eves element: " + element.getDescription(), e);
		}
		
		return null;
	}

    /**
     * Computes the contents description that will be displayed for the current element.
     *
     * @param part the part that triggered the current element update, or <code>null</code>
     * @param selection the new selection, or <code>null</code>
     * @param inputElement the new java element that will be displayed
     * @param localASTMonitor a progress monitor
     * @return the contents description for the provided <code>inputElement</code>
     */
	protected String computeDescription(IWorkbenchPart part, ISelection selection, IZEvesElement inputElement, IProgressMonitor localASTMonitor) {
		
		if (inputElement == null) {
			return null;
		}
		
		return inputElement.getDescription();
	}

    private void doSetInput(Object input, String description) {
            
    	String inputText = input != null ? input.toString() : "";
    	
    	setText(inputText);
    	
    	setContentDescription(description);
    	setTitleToolTip(description);
    }
    
    private boolean isSelectionInteresting(IWorkbenchPart part, ISelection selection) {
    	
    	if (selection == null) {
    		return false;
    	}
    	
    	if (selection instanceof ITextSelection && part instanceof ZEditor) {
    		return true;
    	}
    	
    	return !selection.isEmpty();
    }
    
    private int getCaretPosition(IWorkbenchPart part) {
    	if (part instanceof ZEditor) {
    		return ZEditorUtil.getCaretPosition((ZEditor) part);
    	}
    	
    	return -1;
    }
    
    /**
     * Action to toggle linking with selection.
     */
	private class LinkAction extends Action {

		public LinkAction() {
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
		public void run() {
			setLinkingEnabled(!isLinkingEnabled());
		}
	}
	
	private class ForceUnicodeAction extends Action {

		public ForceUnicodeAction() {
			super("Force Unicode", SWT.TOGGLE);
			setToolTipText("Force Unicode");

			// setDescription("?");
			setImageDescriptor(ZEvesImages.getImageDescriptor(ZEvesImages.IMG_UNICODE));

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
			boolean forceUnicode = preferenceStore.getBoolean(PROP_FORCE_UNICODE);
			setForceUnicode(forceUnicode);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		public void run() {
			setForceUnicode(!forceUnicode);

			if (currentViewInput != null) {
				setInput(currentViewInput);
			}
		}

		private void setForceUnicode(boolean force) {
			forceUnicode = force;
			setChecked(force);

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
			preferenceStore.setValue(PROP_FORCE_UNICODE, force);
		}
	}

}
