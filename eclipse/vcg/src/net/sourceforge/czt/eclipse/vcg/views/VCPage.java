package net.sourceforge.czt.eclipse.vcg.views;

import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil.ReconcileRunnable;
import net.sourceforge.czt.eclipse.vcg.VcgImages;
import net.sourceforge.czt.eclipse.vcg.VcgPlugin;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.print.zeves.PrintUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.AbstractVCG;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.VCGUtils;
import net.sourceforge.czt.vcg.z.dc.DomainCheckerVCG;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityPropertyKeys;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCG;
import net.sourceforge.czt.vcg.z.refinement.RefinementVCG;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.part.Page;

import static net.sourceforge.czt.eclipse.vcg.IVcgConstants.PREF_SHOW_IN_SPEC_VCS; 

public class VCPage extends Page {

	private Composite main;
	private VCTree filteredTree;
	
	private Action refreshAction;
	private Action insertCursorAction;
	
	private final VCView view;
	private final ZEditor editor;
	private final InSpecFilter inSpecFilter = new InSpecFilter(getShowInSpecPref());
	
	private static boolean getShowInSpecPref() {
		return getPrefs().getBoolean(PREF_SHOW_IN_SPEC_VCS, false);
	}
	
	private static IEclipsePreferences getPrefs() {
		return InstanceScope.INSTANCE.getNode(VcgPlugin.PLUGIN_ID);
	}

	public VCPage(VCView view, ZEditor editor) {
		super();
		this.view = view;
		this.editor = editor;
	}

	@Override
	public void createControl(Composite parent) {
		
		main = new Composite(parent, SWT.NONE);
		main.setLayout(GridLayoutFactory.fillDefaults().extendedMargins(0, 0, 2, 0).create());

		createActions();
		
        createFilteredTree(main);
        filteredTree.setInput(Collections.<VCEntry>emptyList());

		initToolBar();
		
		updateVCList(false);
		
		// register as global selection provider
		getSite().setSelectionProvider(filteredTree.getViewer());
	}

	@Override
	public Control getControl() {
		return main;
	}

	@Override
	public void setFocus() {
		filteredTree.setFocus();
	}
	
    private void createFilteredTree(Composite parent) {
    	
    	filteredTree = new VCTree(parent, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI);

        filteredTree.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());
        
        filteredTree.getViewer().getTree().addSelectionListener(new SelectionAdapter() {
            @Override
			public void widgetDefaultSelected(SelectionEvent e) {
                handleDefaultSelected();
            }
        });
        
        filteredTree.getViewer().addSelectionChangedListener(new ISelectionChangedListener() {
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				handleSelectionChanged();
			}
		});
        
        filteredTree.getViewer().addFilter(inSpecFilter);
        
        // add context menu
        final MenuManager mgr = new MenuManager();
        mgr.add(insertCursorAction);
        Control tree = filteredTree.getViewer().getTree();
        tree.setMenu(mgr.createContextMenu(tree));
    }
    
    /**
     * Handles a selection changed event.
     */
    private void handleSelectionChanged() {
    	insertCursorAction.setEnabled(!getSelection().isEmpty());
    }
    
    private IStructuredSelection getSelection() {
    	return (IStructuredSelection) filteredTree.getViewer().getSelection();
    }
    
    /**
     * Handles default selection (double click).
     */
    private void handleDefaultSelected() {
    	IStructuredSelection sel = getSelection();
    	if (sel.isEmpty()) {
    		return;
    	}
    	
    	insertSelectedVCs(sel);
    }
    
    private void createActions() {
    	refreshAction = new RefreshTheoremsAction();
    	insertCursorAction = new InsertVCsCursorAction();
    }
    
    
	private void initToolBar() {
		IActionBars bars = getSite().getActionBars();
		IToolBarManager tm = bars.getToolBarManager();
		tm.add(new ShowInSpecAction());
		tm.add(refreshAction);
	}
	
	private void insertSelectedVCs(IStructuredSelection sel) {
		if (sel.isEmpty()) {
			return;
		}

		// separate paragraphs with double newline
		String paraSep = "\n\n";

		StringBuilder vcInsert = new StringBuilder(); 
		for (Iterator<?> it = sel.iterator(); it.hasNext(); ) {
			VCEntry vcEntry = (VCEntry) it.next();
			
			vcInsert.append(paraSep);
			try {
				vcInsert.append(printVC(vcEntry));
			} catch (Exception ex) {
				MessageDialog.openError(getSite().getShell(), "Problems Printing VC",
						"Cannot print VC: " + ex.getMessage());
				VcgPlugin.getDefault().log(ex);
			}
		}
		
		IDocument document = ZEditorUtil.getDocument(editor);
		int offset = getEditorInsertOffset(document);
		
		// insert generated
		try {
			
			document.replace(offset, 0, vcInsert.toString());
			editor.getViewer().setSelectedRange(offset, vcInsert.length());
			
		} catch (BadLocationException e) {
			VcgPlugin.getDefault().log(e);
		}
		
		// wait for reconcile (parsing) and refresh
		ZEditorUtil.runOnReconcile(editor, new ReconcileRunnable() {
			
			@Override
			protected void run(ParsedData parsedData) {
				updateVCList(false);
			}
		});
	}
	
	private int getEditorInsertOffset(IDocument document) {
		int caretPos = ZEditorUtil.getCaretPosition(editor);
		
		int insertPos = findParaInsert(editor.getParsedData(), caretPos);
		if (insertPos < 0) {
			// could not find one - just insert at the end of document
			insertPos = document.getLength();
		}
		
		return insertPos;
	}
	
	/**
	 * Finds the end position of the first paragraph, that is after/including
	 * the given cursor position.
	 * 
	 * @param parsedData
	 * @param cursorPos
	 * @return
	 */
	private int findParaInsert(ParsedData parsedData, int cursorPos) {
		
		if (parsedData == null) {
			return -1;
		}
		
		Spec spec = parsedData.getSpec();
		if (spec == null) {
			return -1;
		}
		
		for (Sect sect : spec.getSect()) {
			if (sect instanceof ZSect) {
				for (Para para : ((ZSect) sect).getZParaList()) {
					Position paraPos = parsedData.getTermPosition(para);
					if (paraPos != null) {
						
						int end = paraPos.getOffset() + paraPos.getLength();
						if (cursorPos <= end) {
							// found first para encompassing cursor
							if (para instanceof NarrPara) {
								// narrative paragraph - actually insert at cursor then
								return cursorPos;
							}
							
							return end;
						}
						
					}
				}
			}
		}
		
		return -1;
	}
	
	public String printVC(VCEntry vcEntry) throws CommandException {
		
		SectionManager sectMan = vcEntry.getSectionManager().clone();

		// TODO externalise preferences?
		sectMan.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, String.valueOf(80));
		sectMan.setProperty(PrintPropertiesKeys.PROP_PRINT_ZEVES, "true");

		/*
		 * FIXME fix the section-based printing. Currently the problem is that
		 * there is no way of passing in a section name for a term, therefore
		 * operators fail.
		 */
//		String keyId = "vc-print";
//		sectMan.put(new Key<Term>(keyId, Term.class), vcEntry.getVCPara());
//		CztPrintString out = sectMan.get(getPrintKey(keyId, vcEntry.getEditor().getMarkup()));
		
		StringWriter out = new StringWriter();

		PrintUtils.print(vcEntry.getVCPara(), out, sectMan, 
				vcEntry.getSectionName(), vcEntry.getEditor().getMarkup());
		
		return out.toString();
	}
	
	private Key<? extends CztPrintString> getPrintKey(String keyId, Markup markup) {
		switch (markup) {
		case UNICODE: return new Key<UnicodeString>(keyId, UnicodeString.class);
		case ZML: return new Key<XmlString>(keyId, XmlString.class);
		// use LaTeX by default
		case LATEX: 
		default: return new Key<LatexString>(keyId, LatexString.class);
		}
	}

	private void updateVCList(boolean user) {
		
		ParsedData parsedData = editor.getParsedData();
		if (parsedData == null || parsedData.getSpec() == null
				|| parsedData.getSectionManager() == null) {
			// do not launch the job if nothing is available
			filteredTree.setInput(Collections.<VCEntry>emptyList());
			return;
		}
		
		VCRefreshJob refreshJob = new VCRefreshJob(parsedData);
		
		refreshJob.setUser(user);
		refreshJob.schedule();
	}
	
	private class VCRefreshJob extends Job {

		private final ParsedData parsedData;
		private String viewMsg;
		
		public VCRefreshJob(ParsedData parsedData) {
			super("Generating verification conditions");
			this.parsedData = parsedData;
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			setViewMsg("");
			
			final List<VCEntry> vcs = new ArrayList<VCEntry>();
			
			try {
				vcs.addAll(createVCs(monitor));
			} catch (VCGException e) {
				Throwable summary = handleVCException(e);
				return VcgPlugin.newErrorStatus(summary.getMessage(), summary);
			} catch (CommandException e) {
				return VcgPlugin.newErrorStatus(e.getMessage(), e);
			}
			
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			// sort by VC name
			Collections.sort(vcs, new Comparator<VCEntry>() {
				@Override
				public int compare(VCEntry o1, VCEntry o2) {
					return o1.getVCName().compareTo(o2.getVCName());
				}
			});
			
			getSite().getShell().getDisplay().asyncExec(new Runnable() {
				@Override
				public void run() {
					view.setViewMessage(VCPage.this, viewMsg);
					filteredTree.setInput(vcs);
				}
			});
			
			return Status.OK_STATUS;
		}
		
		private List<VCEntry> createVCs(IProgressMonitor monitor) throws CommandException {
			
			if (parsedData == null || parsedData.getSpec() == null
					|| parsedData.getSectionManager() == null) {
				
				setViewMsg("No VCs generated: editor contents are not available");
				return Collections.emptyList();
			}
			
			if (ZEditorUtil.hasErrors(parsedData)) {
				// type or parsing errors, do not generate VCs
				setViewMsg("No VCs generated: editor has unsolved problems");
				return Collections.emptyList();
			}
			
			List<VCEntry> vcs = new ArrayList<VCEntry>();

//			vcs.addAll(createVCs(initDomainVcg()));
			vcs.addAll(createVCs(initFeasibilityVcg()));
			
			return vcs;
		}

		private List<VCEntry> createVCs(AbstractVCG<Pred> fsbVcg) throws CommandException {
			List<VCEntry> vcs = new ArrayList<VCEntry>();
			
			for (Sect sect : parsedData.getSpec().getSect()) {
				if (sect instanceof ZSect) {
					VCManager vcManager = new VCManager(editor, fsbVcg, parsedData, (ZSect) sect);
					vcs.addAll(vcManager.generateVCs());
				}
			}
			
			return vcs;
		}

		private FeasibilityVCG initFeasibilityVcg() throws VCGException {

			SectionManager sectInfo = parsedData.getSectionManager().clone();
			
			// set the flag to generate Schema-based VCs
			sectInfo.setProperty(FeasibilityPropertyKeys.PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS,
					String.valueOf(true));
//			sectInfo.setTracing(true);
//			sectInfo.setTracingLevel(Level.ALL);
			
			FeasibilityVCG fsbVcg = new RefinementVCG();//new FeasibilityVCG();
			fsbVcg.setSectionManager(sectInfo);
			return fsbVcg;
		}
		
		private DomainCheckerVCG initDomainVcg() throws VCGException {

			SectionManager sectInfo = parsedData.getSectionManager().clone();
			
			DomainCheckerVCG dcVcg = new DomainCheckerVCG();
			dcVcg.setSectionManager(sectInfo);
			return dcVcg;
		}
		
		private Throwable handleVCException(VCGException e) {
			List<? extends Throwable> exceptions = VCGUtils.handleVCGException(e, "Generating VCs");
			if (exceptions.isEmpty()) {
				// log the main
				VcgPlugin.getDefault().log(e);
				return e;
			}
			
			for (Throwable ex : exceptions) {
				
				StringBuilder errMsg = new StringBuilder();
				if (ex instanceof CztErrorList) {
					List<? extends CztError> errs = ((CztErrorList) ex).getErrors();
					for (CztError err : errs) {
						errMsg.append(err.getMessage());
						errMsg.append("\n");
					}
//					ex = new VCGException(((DefinitionException) ex).getMessage(true), ex);
				}
				
				String msg = errMsg.length() > 0 ? errMsg.toString() : ex.getMessage();

				VcgPlugin.getDefault().log(msg, ex);
			}
		
			// the first one is summary
			return exceptions.get(0);
		}
		
		private void setViewMsg(String message) {
			this.viewMsg = message;
		}
	}
	
	private class RefreshTheoremsAction extends Action {

		public RefreshTheoremsAction() {
			super("Refresh");
			setToolTipText("Show Theorems");
			
			setImageDescriptor(VcgImages.getImageDescriptor(VcgImages.IMG_REFRESH));
		}
		
		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			updateVCList(true);
		}
	}
	
	private class InsertVCsCursorAction extends Action {

		public InsertVCsCursorAction() {
			super("Insert at Cursor");
			setToolTipText("Insert Verification Conditions at Cursor");
			
			setImageDescriptor(VcgImages.getImageDescriptor(VcgImages.IMG_INSERT));
		}
		
		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			insertSelectedVCs(getSelection());
		}
	}
	
	private static class InSpecFilter extends ViewerFilter {

		private boolean showInSpec;
		
		public InSpecFilter(boolean showInSpec) {
			setShowInSpec(showInSpec);
		}
		
		public boolean isShowInSpec() {
			return showInSpec;
		}

		public void setShowInSpec(boolean showInSpec) {
			this.showInSpec = showInSpec;
		}

		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			
			if (((VCEntry) element).isInSpecification()) {
				return showInSpec;
			}
			
			return true;
		}
	}
	
	private class ShowInSpecAction extends Action {

		public ShowInSpecAction() {
			super("Show Existing", SWT.TOGGLE);
			setToolTipText("Show VCs Already in Specification");
			
			setImageDescriptor(VcgImages.getImageDescriptor(VcgImages.IMG_IN_SPEC));
			setChecked(inSpecFilter.isShowInSpec());
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			boolean showInSpec = !inSpecFilter.isShowInSpec();
			inSpecFilter.setShowInSpec(showInSpec);
			getPrefs().putBoolean(PREF_SHOW_IN_SPEC_VCS, showInSpec);
			filteredTree.getViewer().refresh();
		}
	}
	
}
