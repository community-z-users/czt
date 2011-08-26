package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.IZPartitions;
import net.sourceforge.czt.eclipse.editors.FontUpdater;
import net.sourceforge.czt.eclipse.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.preferences.PreferenceConstants;
import net.sourceforge.czt.eclipse.preferences.SimpleZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.actions.SendProofCommand;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ProofResultElement;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ProofResultElement.IProofResultInfo;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.commands.ActionHandler;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchCommandConstants;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.contexts.IContextActivation;
import org.eclipse.ui.contexts.IContextService;
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

	private static final String VIEW_ID = ZEvesPlugin.PLUGIN_ID + ".view.Output";
	private static final String PROP_FORCE_UNICODE = VIEW_ID + ".forceUnicode";
	private static final String PROP_SHOW_INFO = VIEW_ID + ".showProofInfo";
	
	static {
		IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
		preferenceStore.setDefault(PROP_FORCE_UNICODE, false);
	}

	private static final String SELECTION_CMDS_ID = "selectionCmds";
	
	private static final String CONTEXT_TERM = ZEvesPlugin.PLUGIN_ID + ".proof.term";
	private static final String CONTEXT_EXPR = ZEvesPlugin.PLUGIN_ID + ".proof.expr";
	private static final String CONTEXT_PRED = ZEvesPlugin.PLUGIN_ID + ".proof.pred";
	private final Map<String, IContextActivation> contextActivations = new HashMap<String, IContextActivation>();
	
	private Composite main;
	private GridData infoControlData;
	private ZSourceViewer zViewer;
	private Label cmdField;
	private Label infoField;
	
	/** The text context menu to be disposed. */
	private Menu fTextContextMenu;
	
	/**
     * True if linking with selection is enabled, false otherwise.
     */
    private boolean linking= true;
    
    /**
     * Action to enable and disable link with selection.
     */
    private LinkAction toggleLinkAction;
    
    private boolean forceUnicode;
    private boolean showProofInfo;

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
		
		@Override
		public void partVisible(IWorkbenchPartReference ref) {
			if (ref.getId().equals(getSite().getId())) {
				IWorkbenchPart activePart = ref.getPage().getActivePart();
				if (activePart != null) {
					selectionChanged(activePart, ref.getPage().getSelection());
				}
				startListeningForSelectionChanges();
			}
		}

		@Override
		public void partHidden(IWorkbenchPartReference ref) {
			if (ref.getId().equals(getSite().getId()))
				stopListeningForSelectionChanges();
		}

		@Override
		public void partInputChanged(IWorkbenchPartReference ref) {
			if (!ref.getId().equals(getSite().getId()))
				computeAndSetInput(ref.getPart(false));
		}

		@Override
		public void partActivated(IWorkbenchPartReference ref) {
		}

		@Override
		public void partBroughtToTop(IWorkbenchPartReference ref) {
		}

		@Override
		public void partClosed(IWorkbenchPartReference ref) {
		}

		@Override
		public void partDeactivated(IWorkbenchPartReference ref) {
		}

		@Override
		public void partOpened(IWorkbenchPartReference ref) {
		}
	};
	
	@Override
	public void createPartControl(Composite parent) {
		
		main = new Composite(parent, SWT.NONE);
		main.setLayout(GridLayoutFactory.fillDefaults().create());
		
		Control viewerControl = createZViewer(main);
		viewerControl.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());
		
		Control infoControl = createInfoPane(main);
		infoControlData = GridDataFactory.fillDefaults().grab(true, false).create();
		infoControl.setLayoutData(infoControlData);
		
		createActions();
		fillActionBars(getViewSite().getActionBars());
		
		getSite().getWorkbenchWindow().getPartService().addPartListener(partListener);
	}
	
	/**
	 * Copied from net.sourceforge.czt.eclipse.views.ZConversionView
	 * @param parent
	 */
	private Control createZViewer(Composite parent) {
		
		IPreferenceStore generalTextStore = EditorsUI.getPreferenceStore();
		IPreferenceStore store = new ChainedPreferenceStore(new IPreferenceStore[] {
				CZTPlugin.getDefault().getPreferenceStore(), generalTextStore });

		zViewer = new ZSourceViewer(parent, null, null, false, SWT.V_SCROLL | SWT.H_SCROLL, store);

		SimpleZSourceViewerConfiguration configuration = new SimpleZSourceViewerConfiguration(CZTPlugin.getDefault()
				.getCZTTextTools().getColorManager(), store, null, IZPartitions.Z_PARTITIONING, false);
		zViewer.configure(configuration);
		// FIXME implement proper setting of font (according to content displayed)
		FontUpdater.enableFor(zViewer, configuration, store, PreferenceConstants.EDITOR_UNICODE_FONT);
		zViewer.setEditable(false);
		zViewer.setDocument(new Document());
		
		MenuManager manager = new MenuManager();
		manager.setRemoveAllWhenShown(true);
		manager.addMenuListener(new IMenuListener() {
			@Override
			public void menuAboutToShow(IMenuManager menu) {
				setFocus();
				contextMenuAboutToShow(menu);
			}
		});
		
		Control textWidget = zViewer.getTextWidget();
		fTextContextMenu= manager.createContextMenu(textWidget);
		textWidget.setMenu(fTextContextMenu);
		
		getSite().registerContextMenu(manager, zViewer);
		// Make the selection available
		getSite().setSelectionProvider(zViewer);
		
//		getSite().getPage().addPostSelectionListener(VIEW_ID, new ISelectionListener() {
//			
//			@Override
//			public void selectionChanged(IWorkbenchPart part, ISelection selection) {
//				updateSelectionContext();
//			}
//		});
		
		zViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelectionContext();
			}
		});
		
		return zViewer.getControl();
	}
	
	private Control createInfoPane(Composite parent) {
		
		Composite infoPane = new Composite(parent, SWT.NONE);
		infoPane.setLayout(GridLayoutFactory.swtDefaults().numColumns(2).create());
		
		Label cmdLabel = new Label(infoPane, SWT.NONE);
		cmdLabel.setText("Command sent:");
		cmdLabel.setLayoutData(GridDataFactory.swtDefaults().align(SWT.BEGINNING, SWT.BEGINNING).create());
		
		cmdField = new Label(infoPane, SWT.WRAP);
		cmdField.setText("");
		cmdField.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());
		
		Label infoLabel = new Label(infoPane, SWT.NONE);
		infoLabel.setText("Proof info:");
		infoLabel.setLayoutData(GridDataFactory.swtDefaults().align(SWT.BEGINNING, SWT.BEGINNING).create());
		
		infoField = new Label(infoPane, SWT.WRAP);
		infoField.setText("");
		infoField.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());
		
		return infoPane;
	}
	
	private void updateSelectionContext() {
		
		IContextService contextService = (IContextService) getSite().getService(
				IContextService.class);

		deactivateContext(contextService, CONTEXT_TERM);
		deactivateContext(contextService, CONTEXT_EXPR);
		deactivateContext(contextService, CONTEXT_PRED);
		
		Term selectedTerm = getSelectedTerm();
		if (selectedTerm == null) {
			// nothing selected or cannot parse, so no contexts activated
			return;
		}

		activateContext(contextService, CONTEXT_TERM);
		
		if (selectedTerm instanceof Expr) {
			activateContext(contextService, CONTEXT_EXPR);
		}
		
		if (selectedTerm instanceof Pred) {
			activateContext(contextService, CONTEXT_PRED);
		}
	}
	
	private void activateContext(IContextService contextService, String contextId) {
		IContextActivation act = contextService.activateContext(contextId);
		contextActivations.put(contextId, act);
	}
	
	private void deactivateContext(IContextService contextService, String contextId) {
		IContextActivation act = contextActivations.get(contextId);
		if (act != null) {
			contextService.deactivateContext(act);
			contextActivations.remove(contextId);
		}
	}
	
	protected void contextMenuAboutToShow(IMenuManager menu) {

		menu.add(new Separator(SELECTION_CMDS_ID));
		
		MenuManager applyMenu = getApplySubmenu();
		if (applyMenu != null) {
			menu.add(applyMenu);
		}
	}
	
	private MenuManager getApplySubmenu() {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			return null;
		}
		
		ZEvesApi api = prover.getApi();
		
		if (!(currentViewInput instanceof ProofResultElement)) {
			return null;
		}
		
		ProofResultElement proofResult = (ProofResultElement) currentViewInput;
		Integer zEvesStepIndex = proofResult.getZEvesStepIndex();
		if (zEvesStepIndex == null) {
			// no step index, cannot determine the rules
			return null;
		}
		
		Term selectedTerm = getSelectedTerm();
		
		if (selectedTerm == null) {
			return null;
		}
		
		SectionManager sectInfo = proofResult.getEditor().getParsedData().getSectionManager().clone();
		String sectName = proofResult.getSectionName();
		
		String exprStr = printTerm(selectedTerm, sectInfo, sectName);
		
		String menuLabel;
		List<String> applyRules;
		String cmdFormat;
		
		if (selectedTerm instanceof Expr) {
			menuLabel = "Apply To Expression";
			cmdFormat = "apply %1$s to expression %2$s";
			try {
				applyRules = api.getRulesMatchingExpression(proofResult.getGoalName(),
						zEvesStepIndex.intValue(), exprStr);
			} catch (ZEvesException e) {
				ZEvesPlugin.getDefault().log(e);
				return null;
			}
		} else if (selectedTerm instanceof Pred) {
			menuLabel = "Apply To Predicate";
			cmdFormat = "apply %1$s to predicate %2$s";
			try {
				applyRules = api.getRulesMatchingPredicate(proofResult.getGoalName(),
						zEvesStepIndex.intValue(), exprStr);
			} catch (ZEvesException e) {
				ZEvesPlugin.getDefault().log(e);
				return null;
			}
		} else {
			return null;
		}
		
		if (applyRules.isEmpty()) {
			return null;
		}
		
		MenuManager applyMenu = new MenuManager(menuLabel);
		
		for (String rule : applyRules) {
			applyMenu.add(new SendApplyAction(rule, cmdFormat, selectedTerm, proofResult));
		}
		return applyMenu;
	}
	
	private String printTerm(Term term, SectionInfo sectInfo, String sectionName) {
		CZT2ZEvesPrinter printer = new CZT2ZEvesPrinter(sectInfo);
		printer.setSectionName(sectionName);
		return term.accept(printer);
	}
	
	private Term getSelectedTerm() {
		
		ITextSelection selection = (ITextSelection) zViewer.getSelection();
		if (selection.isEmpty()) {
			return null;
		}
		
		if (!(currentViewInput instanceof ProofResultElement)) {
			return null;
		}
		
		ProofResultElement proofResult = (ProofResultElement) currentViewInput;
		ZEditor editor = proofResult.getEditor();
		
		String selectedText = selection.getText();
		SectionManager sectInfo = editor.getParsedData().getSectionManager().clone();
		String sectName = proofResult.getSectionName();
		
		try {
			return ZEvesResultConverter.parseZEvesResult(sectInfo, sectName, selectedText);
		} catch (IOException e) {
			// unexpected exception - log and return
			ZEvesPlugin.getDefault().log(e);
			return null;
		} catch (CommandException e) {
			// cannot parse
			return null;
		}
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
    	tbm.add(new ShowProofInfoAction());
    	tbm.add(toggleLinkAction);
    }


	@Override
	public void dispose() {
		getSite().getWorkbenchWindow().getPartService().removePartListener(partListener);
		
		if (fTextContextMenu != null) {
			fTextContextMenu.dispose();
			fTextContextMenu= null;
		}
		
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
	@Override
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
		
		if (element instanceof IAdaptable) {
			ze = (IZEvesElement) ((IAdaptable) element).getAdapter(IZEvesElement.class);
		}

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
					@Override
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
		
//		setContentDescription("");

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
    	
    	String inputText;
    	String cmdText;
    	String infoText;
    	if (input instanceof IProofResultInfo) {
    		IProofResultInfo res = (IProofResultInfo) input;
    		inputText = res.getResult();
    		cmdText = res.getCommand();
    		infoText = res.getInfo();
    	} else {
    		inputText = input != null ? input.toString() : "";
    		cmdText = null;
    		infoText = null;
    	}
    	
    	setText(inputText);
    	
    	setContentDescription(description);
    	setTitleToolTip(description);
    	
    	cmdField.setText(cmdText != null ? cmdText : "");
    	infoField.setText(infoText != null ? infoText : "");
    	
    	main.layout(true);
//    	main.pack(true);
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
    
    public IZEvesElement getCurrentInput() {
    	return currentViewInput;
    }
    
    private void updateProofInfoPane() {
    	
    	boolean showing = !infoControlData.exclude;
    	if (showProofInfo != showing) {
    		infoControlData.exclude = !showProofInfo;
    		main.layout(true);
    	}
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
		@Override
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
	
	private class ShowProofInfoAction extends Action {

		public ShowProofInfoAction() {
			super("Show Info", SWT.TOGGLE);
			setToolTipText("Show Proof Info");

			// setDescription("?");
			ISharedImages images = PlatformUI.getWorkbench().getSharedImages();
			setImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
			boolean showProofInfo = preferenceStore.getBoolean(PROP_SHOW_INFO);
			setShowProofInfo(showProofInfo);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			setShowProofInfo(!showProofInfo);
		}

		private void setShowProofInfo(boolean show) {
			showProofInfo = show;
			setChecked(show);
			
			updateProofInfoPane();

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
			preferenceStore.setValue(PROP_SHOW_INFO, show);
		}
	}
	
	private class SendApplyAction extends Action {
		
		private final String cmdName;
		private final String cmdFormat;
		private final Term term;
		
		private final ProofResultElement proofResult;
		
		public SendApplyAction(String cmdName, String cmdFormat, Term term,
				ProofResultElement proofResult) {
			super(cmdName);
			
			this.cmdName = cmdName;
			this.cmdFormat = cmdFormat;
			this.term = term;
			this.proofResult = proofResult;
			
			// do not print the term yet, just use ... instead
			setToolTipText(getProofCmd("..."));
			
			// setDescription("?");
//			setImageDescriptor(ZEvesImages.getImageDescriptor(ZEvesImages.IMG_UNICODE));
		}
		
		private String getProofCmd(String termStr) {
			return String.format(cmdFormat, cmdName, termStr);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			
			ZEditor editor = proofResult.getEditor();
			SectionManager sectInfo = editor.getParsedData().getSectionManager().clone();
			String sectName = proofResult.getSectionName();
			
			String param = ZEvesResultConverter.printResult(sectInfo, sectName, term,
					editor.getMarkup(), -1);
			
			String proofCommand = getProofCmd(param.trim());
			try {
				SendProofCommand.addSubmitCommand(proofResult, proofCommand);
			} catch (ExecutionException e) {
				ZEvesPlugin.getDefault().log(e);
			}
		}
		
	}

}
