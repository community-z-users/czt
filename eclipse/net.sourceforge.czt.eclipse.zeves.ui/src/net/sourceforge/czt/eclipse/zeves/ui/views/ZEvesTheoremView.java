package net.sourceforge.czt.eclipse.zeves.ui.views;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.views.TheoremTree.TheoremEntry;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ZEvesApi.ZEvesTheoremType;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.part.ViewPart;

/**
 * @author Andrius Velykis
 */
public class ZEvesTheoremView extends ViewPart {

	private Action refreshAction;
	
    /**
     * Action to enable and disable showing of axioms.
     */
    private ShowAxiomsAction toggleAxiomsAction;
	
    private TheoremTree filteredTree;
    private final AxiomFilter axiomFilter = new AxiomFilter(true);

	@Override
	public void createPartControl(Composite parent) {
		
		Composite main = new Composite(parent, SWT.NONE);
		main.setLayout(GridLayoutFactory.fillDefaults().extendedMargins(0, 0, 2, 0).create());
		
        createFilteredTree(main);
        filteredTree.setInput(Collections.<TheoremEntry>emptyList());

        createActions();
		initToolBar();
		
		updateTheoremList(false);
		
		// register as global selection provider
		getSite().setSelectionProvider(filteredTree.getViewer());
	}

	@Override
	public void setFocus() {
		filteredTree.setFocus();
	}
    
    /**
     * Handles a selection changed event.
     */
    private void handleSelectionChanged() {
//        validateCurrentSelection();
    }
    
    /**
     * Handles default selection (double click).
     */
    private void handleDefaultSelected() {
//        if (validateCurrentSelection()) {
//			buttonPressed(IDialogConstants.OK_ID);
//		}
    }

    private void createFilteredTree(Composite parent) {
    	
    	filteredTree = new TheoremTree(parent, SWT.V_SCROLL | SWT.H_SCROLL | SWT.SINGLE);

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
        
        filteredTree.getViewer().addFilter(axiomFilter);
    }
    
    private void createActions() {
    	refreshAction = new RefreshTheoremsAction();
        toggleAxiomsAction = new ShowAxiomsAction();
    }
    
	private void initToolBar() {
		IActionBars bars = getViewSite().getActionBars();
		IToolBarManager tm = bars.getToolBarManager();
		tm.add(toggleAxiomsAction);
		tm.add(refreshAction);
	}

	private void updateTheoremList(boolean user) {
		
		ZEves prover = ZEvesCore.getZEves();
		
		ZEvesApi api = prover.getApi();
		
		if (api == null || !api.isConnected()) {
			if (user) {
				MessageDialog.openError(getSite().getShell(), 
						"Prover Not Connected",
						"The Z/EVES prover is not connected.");
			}
			return;
		}
		
		TheoremRefreshJob refreshJob = new TheoremRefreshJob(api);
		
		refreshJob.setUser(user);
		refreshJob.schedule();
	}
	
	private class TheoremRefreshJob extends Job {

		private final ZEvesApi api;
		
		public TheoremRefreshJob(ZEvesApi api) {
			super("Refreshing Z/EVES theorems");
			this.api = api;
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			final List<TheoremEntry> theorems = new ArrayList<TheoremEntry>();
			
			try {
				int historyLength = api.getHistoryLength();
				
				if (monitor.isCanceled()) {
					return Status.CANCEL_STATUS;
				}
				
				for (int index = 1; index <= historyLength; index++) {
					
					if (monitor.isCanceled()) {
						return Status.CANCEL_STATUS;
					}
					
					Map<String, ZEvesTheoremType> theoremNames = api.getTheoremNames(index);
					for (Entry<String, ZEvesTheoremType> entry : theoremNames.entrySet()) {
						
						if (monitor.isCanceled()) {
							return Status.CANCEL_STATUS;
						}
						
						String theoremName = entry.getKey();
						ZEvesTheoremType type = entry.getValue();
						
						Boolean proved = null;
						if (type == ZEvesTheoremType.GOAL) {
							proved = api.getGoalProvedState(theoremName);
						}
						
						theorems.add(new TheoremEntry(theoremName, type, index, proved));
					}
				}
				
			} catch (ZEvesException e) {
				return ZEvesUIPlugin.newErrorStatus(e.getMessage(), e);
			}
			
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			// sort by theorem name
			Collections.sort(theorems, new Comparator<TheoremEntry>() {
				@Override
				public int compare(TheoremEntry o1, TheoremEntry o2) {
					return o1.getTheoremName().compareTo(o2.getTheoremName());
				}
			});
			
			PlatformUtil.runInUI(new Runnable() {
				public void run() {
					filteredTree.setInput(theorems);
				}
			});
			
			return Status.OK_STATUS;
		}
		
	}
	
	private static class AxiomFilter extends ViewerFilter {

		private boolean showAxioms;
		
		public AxiomFilter(boolean showAxioms) {
			setShowAxioms(showAxioms);
		}
		
		public boolean isShowAxioms() {
			return showAxioms;
		}

		public void setShowAxioms(boolean showAxioms) {
			this.showAxioms = showAxioms;
		}

		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			
			ZEvesTheoremType type = ((TheoremEntry) element).getType();
			
			if (type == ZEvesTheoremType.AXIOM) {
				return showAxioms;
			}
			
			return true;
		}
	}
	
	private class RefreshTheoremsAction extends Action {

		public RefreshTheoremsAction() {
			super("Refresh");
			setToolTipText("Show Theorems");
			
			setImageDescriptor(ZEvesImages.REFRESH);
		}
		
		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			updateTheoremList(true);
		}
	}
	
	private class ShowAxiomsAction extends Action {

		public ShowAxiomsAction() {
			super("Show Axioms", SWT.TOGGLE);
			setToolTipText("Show Axioms in Theorems");
			
			setImageDescriptor(ZEvesImages.THEOREM_AXIOM);
			setChecked(axiomFilter.isShowAxioms());
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			axiomFilter.setShowAxioms(!axiomFilter.isShowAxioms());
			filteredTree.getViewer().refresh();
		}
	}
	
}
