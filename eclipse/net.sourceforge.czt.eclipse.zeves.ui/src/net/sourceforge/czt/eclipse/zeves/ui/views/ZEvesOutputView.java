package net.sourceforge.czt.eclipse.zeves.ui.views;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.views.IZInfoObject;
import net.sourceforge.czt.eclipse.ui.views.ZInfoView;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.actions.SendProofCommand;
import net.sourceforge.czt.eclipse.zeves.ui.editor.ZEvesMarkers;
import net.sourceforge.czt.eclipse.zeves.ui.editor.ZEvesMarkers.MarkerInfo;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IProofObject;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IZEditorObject;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IZEvesInfoProvider;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IZInfoConfiguration;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.snapshot.ISnapshotChangedListener;
import net.sourceforge.czt.zeves.snapshot.ISnapshotEntry;
import net.sourceforge.czt.zeves.snapshot.SnapshotChangedEvent;
import net.sourceforge.czt.zeves.snapshot.SnapshotChangedEvent.SnapshotChangeType;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.contexts.IContextActivation;
import org.eclipse.ui.contexts.IContextService;

/**
 * @author Andrius Velykis
 */
public class ZEvesOutputView extends ZInfoView implements ISelectionListener {

	public static final String VIEW_ID = ZEvesUIPlugin.PLUGIN_ID + ".views.Output";
	private static final String PROP_SHOW_TRACE = VIEW_ID + ".showProofInfo";
	private static final String PROP_SHOW_OUTPUT_SELECTION = VIEW_ID + ".showOutputSelection";
	
	private IMarker editorMarker = null;
	
	static {
		IPreferenceStore preferenceStore = ZEvesUIPlugin.getDefault().getPreferenceStore();
		preferenceStore.setDefault(PROP_SHOW_TRACE, false);
		preferenceStore.setDefault(PROP_SHOW_OUTPUT_SELECTION, true);
	}

	private static final String SELECTION_CMDS_ID = "selectionCmds";
	
	private static final String CONTEXT_TERM = ZEvesUIPlugin.PLUGIN_ID + ".proof.term";
	private static final String CONTEXT_EXPR = ZEvesUIPlugin.PLUGIN_ID + ".proof.expr";
	private static final String CONTEXT_PRED = ZEvesUIPlugin.PLUGIN_ID + ".proof.pred";
	private final Map<String, IContextActivation> contextActivations = new HashMap<String, IContextActivation>();
	
	private boolean showProofTrace;
    private boolean showOutputSelection;
    
    private ISnapshotChangedListener snapshotListener = new EntryRemovedListener();

	@Override
	public void createPartControl(final Composite parent) {
		
		super.createPartControl(parent);
		
		ZEvesCore.getSnapshot().addSnapshotChangedListener(snapshotListener);
		
		getViewer().getSelectionProvider().addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelectionContext();
			}
		});
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
	
	@Override
	public void dispose() {
		ZEvesCore.getSnapshot().removeSnapshotChangedListener(snapshotListener);
		super.dispose();
	}

	@Override
	protected void contextMenuAboutToShow(IMenuManager menu) {

		super.contextMenuAboutToShow(menu);
		
		menu.add(new Separator(SELECTION_CMDS_ID));
		
		MenuManager applyMenu = getApplySubmenu();
		if (applyMenu != null) {
			menu.add(applyMenu);
		}
	}
	
	public IProofObject getCurrentProof() {
		
		IZInfoObject input = getCurrentInput();
		if (input instanceof IProofObject) {
			return (IProofObject) input;
		}
		
		if (input instanceof IAdaptable) {
			return (IProofObject) ((IAdaptable) input).getAdapter(IProofObject.class);
		}
		
		return null;
	}
	
	private MenuManager getApplySubmenu() {
		
		ZEves prover = ZEvesCore.getZEves();
		if (!prover.isRunning()) {
			return null;
		}
		
		ZEvesApi api = prover.getApi();
		
		IProofObject proofResult = getCurrentProof();
		if (proofResult == null) {
			return null;
		}
		
		Integer zEvesStepIndex = proofResult.getZEvesStepIndex();
		if (zEvesStepIndex == null) {
			// no step index, cannot determine the rules
			return null;
		}
		
		Term selectedTerm = getSelectedTerm();
		
		if (selectedTerm == null) {
			return null;
		}
		
		SectionManager sectInfo = proofResult.getSectionManager().clone();
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
				ZEvesUIPlugin.getDefault().log(e);
				return null;
			}
		} else if (selectedTerm instanceof Pred) {
			menuLabel = "Apply To Predicate";
			cmdFormat = "apply %1$s to predicate %2$s";
			try {
				applyRules = api.getRulesMatchingPredicate(proofResult.getGoalName(),
						zEvesStepIndex.intValue(), exprStr);
			} catch (ZEvesException e) {
				ZEvesUIPlugin.getDefault().log(e);
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
		
		ITextSelection selection = (ITextSelection) getViewer().getSelectionProvider().getSelection();
		if (selection.isEmpty()) {
			return null;
		}
		
		IProofObject proofResult = getCurrentProof();
		if (proofResult == null) {
			return null;
		}
		
		String selectedText = selection.getText();
		SectionManager sectInfo = proofResult.getSectionManager().clone();
		String sectName = proofResult.getSectionName();
		
		try {
			return ZEvesResultConverter.parseZEvesResult(sectInfo, sectName, selectedText);
		} catch (IOException e) {
			// unexpected exception - log and return
			ZEvesUIPlugin.getDefault().log(e);
			return null;
		} catch (CommandException e) {
			// cannot parse
			return null;
		}
	}
	
    /**
     * Fills the tool bar.
     * <p>
     *
     * @param tbm the tool bar manager
     */
    @Override
	protected void fillToolBar(IToolBarManager tbm) {
    	super.fillToolBar(tbm);
    	tbm.appendToGroup(TOOLBAR_GROUP_INFO_VIEW, new ShowProofTraceAction());
    	tbm.add(new ShowOutputSelectionAction());
    }
	
    @Override
	protected IZInfoObject findSelectedZInfoElement(IWorkbenchPart part, ISelection selection, int caretPos) {
		
		if (part instanceof IZEditor && selection instanceof ITextSelection) {
			return ZEditorResults.getZEvesResult((IZEditor) part, caretPos);
		}
    	
		return super.findSelectedZInfoElement(part, selection, caretPos);
	}
    
    @Override
	protected Object loadContents(IWorkbenchPart part, ISelection selection, IZInfoObject element,
			IProgressMonitor monitor) {

		if (element instanceof IZEvesInfoProvider) {
			try {
				return ((IZEvesInfoProvider) element).loadContents(
						getElementMarkup(element), showProofTrace, monitor);
			} catch (CoreException e) {
				CztUIPlugin.log(e);
				return null;
			}
		}

		return super.loadContents(part, selection, element, monitor);
	}

	@Override
	protected void doSetInput(IZInfoObject element, Object input, String description) {
		
		updateEditorMarker(element);
    	super.doSetInput(element, input, description);
	}

	@Override
	protected void setContents(Object input, Markup markup) {
		
		if (input instanceof IZInfoConfiguration) {
			IZInfoConfiguration inputConfig = (IZInfoConfiguration) input;
			// TODO support viewer configurations?
			IDocument document = inputConfig.getDocument();
			
		    setMarkup(markup);
		    
		    IAnnotationModel model = new AnnotationModel();
		    for (Entry<Annotation, Position> annotation : inputConfig.getAnnotations().entrySet()) {
		    	model.addAnnotation(annotation.getKey(), annotation.getValue());
		    }
		    
		    getViewer().setDocument(document, model);
		    
		} else {
			super.setContents(input, markup);
		}
	}

	private void updateEditorMarker(IZInfoObject element) {
		
		if (editorMarker != null) {
			// delete previous marker
			try {
				editorMarker.delete();
			} catch (CoreException e) {
				ZEvesUIPlugin.getDefault().log(e);
			}
			editorMarker = null;
		}
		
		if (!showOutputSelection) {
			return;
		}
		
		if (element instanceof IZEditorObject) {
			IZEditorObject editorObj = (IZEditorObject) element;
			IZEditor editor = editorObj.getEditor();
			
			IResource resource = ZEditorUtil.getEditorResource(editor);
			if (resource != null) {
				
				IDocument document = ZEditorUtil.getDocument(editor);
				Position pos = editorObj.getPosition();
				
				ZEvesMarkers markers = new ZEvesMarkers(resource, document);
				try {
					MarkerInfo markerInfo = markers.createMarker(
							ZEvesMarkers.MARKER_OUTPUT_SELECTION, 0, pos, null, false);
					editorMarker = resource.createMarker(markerInfo.getType());
					editorMarker.setAttributes(markerInfo.getAttributes());
				} catch (CoreException e) {
					ZEvesUIPlugin.getDefault().log(e);
				}
			}
		}
	}
    
    @Override
	protected boolean isSelectionInteresting(IWorkbenchPart part, ISelection selection) {
    	
		if (super.isSelectionInteresting(part, selection)) {
			return true;
		}
		
		if (selection instanceof ITextSelection && part instanceof IZEditor) {
    		return true;
    	}
		
		return false;
	}
    
    private class EntryRemovedListener implements ISnapshotChangedListener {
		
		@Override
		public void snapshotChanged(SnapshotChangedEvent event) {
			if (event.getType() == SnapshotChangeType.REMOVE) {
				
				IZInfoObject currentInput = getCurrentInput();
				if (currentInput instanceof IAdaptable) {
					ISnapshotEntry snapshotEntry = (ISnapshotEntry) 
							((IAdaptable) currentInput).getAdapter(ISnapshotEntry.class);
					
					if (snapshotEntry != null && event.getEntries().contains(snapshotEntry)) {
						// the current input snapshot has been removed - 
						// need to reload the output view
						// TODO better reload? clearing at the moment
						
						Display display = getViewSite().getWorkbenchWindow().getWorkbench().getDisplay();
						if (display.isDisposed()) {
							return;
						}
						
						display.asyncExec(new Runnable() {
							@Override
							public void run() {
								doSetInput(null, null, null);
							}
						});
					}
				}
			}
		}
	}
    
	private class ShowProofTraceAction extends Action {

		public ShowProofTraceAction() {
			super("Show Trace", SWT.TOGGLE);
			setToolTipText("Show Proof Trace");

			// setDescription("?");
			ISharedImages images = PlatformUI.getWorkbench().getSharedImages();
			setImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));

			IPreferenceStore preferenceStore = ZEvesUIPlugin.getDefault().getPreferenceStore();
			boolean showProofInfo = preferenceStore.getBoolean(PROP_SHOW_TRACE);
			setShowProofInfo(showProofInfo);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			setShowProofInfo(!showProofTrace);
		}

		private void setShowProofInfo(boolean show) {
			showProofTrace = show;
			setChecked(show);
			
			reload();

			IPreferenceStore preferenceStore = ZEvesUIPlugin.getDefault().getPreferenceStore();
			preferenceStore.setValue(PROP_SHOW_TRACE, show);
		}
	}
	
	private class ShowOutputSelectionAction extends Action {

		public ShowOutputSelectionAction() {
			super("Highlight Position", SWT.TOGGLE);
			setToolTipText("Highlight Position in Editor");

			// setDescription("?");
			setImageDescriptor(ZEvesImages.OUTPUT_SELECTION);

			IPreferenceStore preferenceStore = ZEvesUIPlugin.getDefault().getPreferenceStore();
			boolean showOutputSelection = preferenceStore.getBoolean(PROP_SHOW_OUTPUT_SELECTION);
			setShowOutputSelection(showOutputSelection);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			setShowOutputSelection(!showOutputSelection);
		}

		private void setShowOutputSelection(boolean show) {
			showOutputSelection = show;
			setChecked(show);
			
			updateEditorMarker(getCurrentInput());

			IPreferenceStore preferenceStore = ZEvesUIPlugin.getDefault().getPreferenceStore();
			preferenceStore.setValue(PROP_SHOW_OUTPUT_SELECTION, show);
		}
	}
	
	private class SendApplyAction extends Action {
		
		private final String cmdName;
		private final String cmdFormat;
		private final Term term;
		
		private final IProofObject proofResult;
		
		public SendApplyAction(String cmdName, String cmdFormat, Term term,
				IProofObject proofResult) {
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
			
			IZEditor editor = proofResult.getEditor();
			SectionManager sectInfo = proofResult.getSectionManager().clone();
			String sectName = proofResult.getSectionName();
			
			String param = ZEvesResultConverter.printResult(sectInfo, sectName, term,
					editor.getMarkup(), -1, false);
			
			String proofCommand = getProofCmd(param.trim());
			try {
				SendProofCommand.addSubmitCommand(proofResult, proofCommand);
			} catch (ExecutionException e) {
				ZEvesUIPlugin.getDefault().log(e);
			}
		}
		
	}
	
}
