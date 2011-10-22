package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.IZPartitions;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.views.IZInfoObject;
import net.sourceforge.czt.eclipse.views.ZInfoView;
import net.sourceforge.czt.eclipse.zeves.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.actions.SendProofCommand;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesMarkers;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesMarkers.MarkerInfo;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.IProofTrace;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ZEditorObject;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ZEvesProofObject;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.IProofResultInfo;
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
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
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

	private static final String VIEW_ID = ZEvesPlugin.PLUGIN_ID + ".view.Output";
	private static final String PROP_SHOW_TRACE = VIEW_ID + ".showProofInfo";
	private static final String PROP_SHOW_OUTPUT_SELECTION = VIEW_ID + ".showOutputSelection";
	
	private IMarker editorMarker = null;
	
	static {
		IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
		preferenceStore.setDefault(PROP_SHOW_TRACE, false);
		preferenceStore.setDefault(PROP_SHOW_OUTPUT_SELECTION, true);
	}

	private static final String SELECTION_CMDS_ID = "selectionCmds";
	
	private static final String CONTEXT_TERM = ZEvesPlugin.PLUGIN_ID + ".proof.term";
	private static final String CONTEXT_EXPR = ZEvesPlugin.PLUGIN_ID + ".proof.expr";
	private static final String CONTEXT_PRED = ZEvesPlugin.PLUGIN_ID + ".proof.pred";
	private final Map<String, IContextActivation> contextActivations = new HashMap<String, IContextActivation>();
	
	private boolean showProofTrace;
    private boolean showOutputSelection;

	@Override
	public void createPartControl(Composite parent) {
		
		super.createPartControl(parent);
		
		zViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			
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
	protected void contextMenuAboutToShow(IMenuManager menu) {

		super.contextMenuAboutToShow(menu);
		
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
		
		if (!(getCurrentInput() instanceof ZEvesProofObject)) {
			return null;
		}
		
		ZEvesProofObject proofResult = (ZEvesProofObject) getCurrentInput();
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
		
		if (!(getCurrentInput() instanceof ZEvesProofObject)) {
			return null;
		}
		
		ZEvesProofObject proofResult = (ZEvesProofObject) getCurrentInput();
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
	
	private void setText(String text, PredefinedTokenScanner scanner) {
		
	    Document document = new Document(text);
	    
//		CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
//				document, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
	    
	    String[] contentTypes = scanner.getContentTypes().toArray(new String[0]);
	    IDocumentPartitioner partitioner = new FastPartitioner(scanner, contentTypes);
	    document.setDocumentPartitioner(IZPartitions.Z_PARTITIONING, partitioner);
	    partitioner.connect(document);
	    
	    zViewer.setDocument(document);
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
		
		if (part instanceof ZEditor && selection instanceof ITextSelection) {
			return ZEditorResults.getZEvesResult((ZEditor) part, (ITextSelection) selection, caretPos);
		}
    	
		return super.findSelectedZInfoElement(part, selection, caretPos);
	}
    
    @Override
	protected void doSetInput(IZInfoObject element, String input, String description) {
		super.doSetInput(element, input, description);
		
		updateEditorMarker(element);

		List<IProofResultInfo> proofInfos = new ArrayList<IProofResultInfo>();
		if (element instanceof IAdaptable) {
			
			IAdaptable elementAdapt = (IAdaptable) element;
			
			if (showProofTrace) {
				IProofTrace proofTrace = (IProofTrace) elementAdapt.getAdapter(IProofTrace.class);
				if (proofTrace != null) {
					proofInfos.addAll(proofTrace.getTrace());
				}
			} else {
				IProofResultInfo proofInfo = (IProofResultInfo) elementAdapt.getAdapter(IProofResultInfo.class);
				if (proofInfo != null) {
					proofInfos.add(proofInfo);
				}
			}
		}
		
		if (!proofInfos.isEmpty()) {
    		
    		PredefinedTokenScanner scanner = new PredefinedTokenScanner();
    		String text = printResult(proofInfos, scanner, getElementMarkup(element), showProofTrace);
    		setText(text, scanner);
    		
    	} else {
    		super.doSetInput(element, input, description);
    	}
	}

	private String printResult(List<IProofResultInfo> proofInfos, PredefinedTokenScanner scanner,
			Markup markup, boolean printTrace) {
		
		StringBuilder out = new StringBuilder();
		
		String delim = "";
		for (IProofResultInfo info : proofInfos) {
			
			out.append(delim);
			
			if (printTrace) {
				String commandStr = info.getCommand();
				if (commandStr != null && !commandStr.isEmpty()) {
					out.append("Proof command: " + commandStr + "\n\n");
				}
				
				String infoStr = info.getInfo();
				if (infoStr != null && !infoStr.isEmpty()) {
					out.append(infoStr + "\n\n");
				}
				
			}
			
			String resultStr = info.getResult();
			
			Position resultPos = new Position(out.length(), resultStr.length());
			out.append(resultStr);
			
			String zPartition = markup == Markup.UNICODE ? 
					IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION : 
						IZPartitions.Z_PARAGRAPH_LATEX_ZED;
			scanner.addTokenPosition(resultPos, zPartition);
			
			if (delim.isEmpty()) {
				delim = createProofResultDelimiter(markup == Markup.UNICODE ? 50 : 80);
			}
		}
		
		return out.toString();
	}
	
	private String createProofResultDelimiter(int textWidth) {
		StringBuilder delim = new StringBuilder("\n\n");
		
		for (int index = 0; index < textWidth; index++) {
			delim.append("\u2500");
		}
		
		delim.append("\n\n");
		
		return delim.toString();
	}

	private void updateEditorMarker(IZInfoObject element) {
		
		if (editorMarker != null) {
			// delete previous marker
			try {
				editorMarker.delete();
			} catch (CoreException e) {
				ZEvesPlugin.getDefault().log(e);
			}
			editorMarker = null;
		}
		
		if (!showOutputSelection) {
			return;
		}
		
		if (element instanceof ZEditorObject<?>) {
			ZEditorObject<?> editorObj = (ZEditorObject<?>) element;
			ZEditor editor = editorObj.getEditor();
			
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
					ZEvesPlugin.getDefault().log(e);
				}
			}
		}
	}
    
    @Override
	protected boolean isSelectionInteresting(IWorkbenchPart part, ISelection selection) {
    	
		if (super.isSelectionInteresting(part, selection)) {
			return true;
		}
		
		if (selection instanceof ITextSelection && part instanceof ZEditor) {
    		return true;
    	}
		
		return false;
	}
    
	private class ShowProofTraceAction extends Action {

		public ShowProofTraceAction() {
			super("Show Trace", SWT.TOGGLE);
			setToolTipText("Show Proof Trace");

			// setDescription("?");
			ISharedImages images = PlatformUI.getWorkbench().getSharedImages();
			setImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
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

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
			preferenceStore.setValue(PROP_SHOW_TRACE, show);
		}
	}
	
	private class ShowOutputSelectionAction extends Action {

		public ShowOutputSelectionAction() {
			super("Highlight Position", SWT.TOGGLE);
			setToolTipText("Highlight Position in Editor");

			// setDescription("?");
			setImageDescriptor(ZEvesImages.getImageDescriptor(ZEvesImages.IMG_OUTPUT_SELECTION));

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
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

			IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
			preferenceStore.setValue(PROP_SHOW_OUTPUT_SELECTION, show);
		}
	}
	
	private class SendApplyAction extends Action {
		
		private final String cmdName;
		private final String cmdFormat;
		private final Term term;
		
		private final ZEvesProofObject proofResult;
		
		public SendApplyAction(String cmdName, String cmdFormat, Term term,
				ZEvesProofObject proofResult) {
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
					editor.getMarkup(), -1, false);
			
			String proofCommand = getProofCmd(param.trim());
			try {
				SendProofCommand.addSubmitCommand(proofResult, proofCommand);
			} catch (ExecutionException e) {
				ZEvesPlugin.getDefault().log(e);
			}
		}
		
	}
	
	/**
	 * A custom token scanner for the output view - it allows to pre-set partitions
	 * based on information displayed in the output. This is necessary, for example, to
	 * print predicates that are not wrapped in any Z paragraph, or to distinguish
	 * the inline comments, etc. 
	 * 
	 * @author Andrius Velykis
	 */
	private static class PredefinedTokenScanner extends RuleBasedScanner implements IPartitionTokenScanner {
		
		private final Map<Position, String> tokenPositions = new LinkedHashMap<Position, String>();
		
		public void addTokenPosition(Position pos, String contentType) {
			tokenPositions.put(pos, contentType);
		}
		
		public Set<String> getContentTypes() {
			return new HashSet<String>(tokenPositions.values());
		}
		
		/*
		 * @see ITokenScanner#nextToken()
		 */
		@Override
		public IToken nextToken() {

			fTokenOffset= fOffset;
			fColumn= UNDEFINED;

			if (read() == EOF) {
				return Token.EOF;
			}
			
			unread();
			
			for (Entry<Position, String> tokenPos : tokenPositions.entrySet()) {
				
				Position pos = tokenPos.getKey();
				
				if (pos.overlapsWith(fTokenOffset, fRangeEnd - fTokenOffset)) {
					
					if (fTokenOffset < pos.getOffset()) {
						// the position does not start yet - read up to its start
						read(fTokenOffset, pos.getOffset());
						return Token.UNDEFINED;
					}
					
					int posEnd = pos.getOffset() + pos.getLength();
					
					read(fTokenOffset, posEnd);
					return new Token(tokenPos.getValue());
				}
			}
			
			// nothing found - read to the end
			read(fTokenOffset, fRangeEnd);
			return Token.UNDEFINED;
		}
		
		private void read(int start, int end) {
			for (int i = start; i < end; i++) {
				read();
			}
		}

		@Override
		public void setPartialRange(IDocument document, int offset, int length, String contentType,
				int partitionOffset) {
			// ignore for now?
		}
		
	}

}
