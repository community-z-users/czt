package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.IZPartitions;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.eclipse.views.IZInfoObject;
import net.sourceforge.czt.eclipse.views.ZInfoView;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.actions.SendProofCommand;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ZEvesProofObject;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.IProofResultInfo;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
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
	private static final String PROP_SHOW_INFO = VIEW_ID + ".showProofInfo";
	
	static {
		IPreferenceStore preferenceStore = ZEvesPlugin.getDefault().getPreferenceStore();
		preferenceStore.setDefault(PROP_SHOW_INFO, false);
	}

	private static final String SELECTION_CMDS_ID = "selectionCmds";
	
	private static final String CONTEXT_TERM = ZEvesPlugin.PLUGIN_ID + ".proof.term";
	private static final String CONTEXT_EXPR = ZEvesPlugin.PLUGIN_ID + ".proof.expr";
	private static final String CONTEXT_PRED = ZEvesPlugin.PLUGIN_ID + ".proof.pred";
	private final Map<String, IContextActivation> contextActivations = new HashMap<String, IContextActivation>();
	
	private GridData infoControlData;
	private Label cmdField;
	private Label infoField;
	
    private boolean showProofInfo;

	@Override
	public void createPartControl(Composite parent) {
		
		super.createPartControl(parent);
		
		Control infoControl = createInfoPane(main);
		infoControlData = GridDataFactory.fillDefaults().grab(true, false).create();
		infoControl.setLayoutData(infoControlData);
		updateProofInfoPane();
		
		zViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelectionContext();
			}
		});
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
	
	private void setText(String text) {
		
	    Document document = new Document(text);
	    
		CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
				document, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
	    
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
    	tbm.appendToGroup(TOOLBAR_GROUP_INFO_VIEW, new ShowProofInfoAction());
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
		
		IProofResultInfo proofInfo = null;
		if (element instanceof IAdaptable) {
			proofInfo = (IProofResultInfo) ((IAdaptable) element).getAdapter(IProofResultInfo.class);
		}
		
    	String cmdText;
    	String infoText;
    	if (proofInfo != null) {
    		setText(proofInfo.getResult());
    		cmdText = proofInfo.getCommand();
    		infoText = proofInfo.getInfo();
    	} else {
    		super.doSetInput(element, input, description);
    		cmdText = null;
    		infoText = null;
    	}
    	
    	cmdField.setText(cmdText != null ? cmdText : "");
    	infoField.setText(infoText != null ? infoText : "");
    	
    	main.layout(true);
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
    
    private void updateProofInfoPane() {
    	
    	if (infoControlData == null) {
    		return;
    	}
    	
    	boolean showing = !infoControlData.exclude;
    	if (showProofInfo != showing) {
    		infoControlData.exclude = !showProofInfo;
    		main.layout(true);
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
