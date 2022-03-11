package net.sourceforge.czt.eclipse.zeves.ui.views;

import net.sourceforge.czt.eclipse.ui.CztImages;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesResetCommand;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesUndoSectionCommand;
import net.sourceforge.czt.eclipse.zeves.ui.launch.ZEvesAppLaunch;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ZEvesServer;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot.FileSection;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;


public class ZEvesStateView extends ViewPart {

	private Label proverStateField;
	private Label proverAddressField;
	
	private Label serverStateField;
	
	private Label paragraphCountField;
	
	private TableViewer sectionsViewer;
	private RemoveSectionAction removeSectionAction;
	
	@Override
	public void createPartControl(Composite parent) {
		
		Composite main = new Composite(parent, SWT.NONE);
		main.setLayout(GridLayoutFactory.swtDefaults().create());
		
		createProverComponent(main);
		createServerComponent(main);
		
		createProverDataComponent(main);
		
		createSectionsComponent(main);
		
		Label filler = new Label(main, SWT.NONE);
		filler.setLayoutData(GridDataFactory.fillDefaults().create());
		
		initToolBar();
		
		updateState();
	}
	
	/**
	 * Creates the controls to display prover information
	 * 
	 * @param parent the composite to create the controls in
	 */
	private void createProverComponent(Composite parent) {
		Group group = new Group(parent, SWT.NONE);
		group.setText("Z/EVES prover");
		group.setLayout(GridLayoutFactory.swtDefaults().create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		group.setLayout(GridLayoutFactory.swtDefaults().numColumns(2).create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		proverStateField = createLabelField(group, "State:");
		proverAddressField = createLabelField(group, "Address:");
		
	}
	
	private Label createLabelField(Composite parent, String text) {
		Label portLabel = new Label(parent, SWT.NONE);
		portLabel.setText(text);
		
		Label field = new Label(parent, SWT.NONE);
		field.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		return field;
	}
	

	/**
	 * Creates the controls to display prover information
	 * 
	 * @param parent the composite to create the controls in
	 */
	private void createServerComponent(Composite parent) {
		Group group = new Group(parent, SWT.NONE);
		group.setText("Z/EVES executable");
		group.setLayout(GridLayoutFactory.swtDefaults().create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		group.setLayout(GridLayoutFactory.swtDefaults().numColumns(2).create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		serverStateField = createLabelField(group, "State:");
		
//		Composite buttons = new Composite(group, SWT.NONE);
//		buttons.setLayout(GridLayoutFactory.swtDefaults().margins(0, 0).create());
//		buttons.setLayoutData(GridDataFactory.fillDefaults().create());
//		
//		Button stopButton = new Button(buttons, SWT.PUSH | SWT.FLAT);
//		stopButton.setFont(parent.getFont());
//		stopButton.setImage(PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_ELCL_STOP));
//		stopButton.setText("Stop");
//		buttons.setLayoutData(GridDataFactory.swtDefaults().create());
//		
//		stopButton.addSelectionListener(new SelectionAdapter() {
//			
//			@Override
//			public void widgetSelected(SelectionEvent e) {
//				ZEvesServer server = ZEvesPlugin.getZEves().getServer();
//				if (server != null) {
//					server.stop();
//					updateState();
//				}
//			}
//		});
	}
	
	/**
	 * Creates the controls to display prover information
	 * 
	 * @param parent the composite to create the controls in
	 */
	private void createProverDataComponent(Composite parent) {
		Group group = new Group(parent, SWT.NONE);
		group.setText("Prover data");
		group.setLayout(GridLayoutFactory.swtDefaults().create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		group.setLayout(GridLayoutFactory.swtDefaults().numColumns(2).create());
		group.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		paragraphCountField = createLabelField(group, "Paragraphs:");
	}
	
	/**
	 * Creates the table to display loaded sections
	 * 
	 * @param parent the composite to create the controls in
	 */
	private void createSectionsComponent(Composite parent) {
		
		Label label = new Label(parent, SWT.NONE);
		label.setText("Submitted sections:");
		label.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());
		
		sectionsViewer = new TableViewer(parent, SWT.SINGLE | SWT.NO_SCROLL | SWT.V_SCROLL
				| SWT.FULL_SELECTION | SWT.BORDER);
		
		TableViewerColumn viewerColumn = new TableViewerColumn(sectionsViewer, SWT.NONE);
		final TableColumn column = viewerColumn.getColumn();
		column.setText("Section");
		column.setWidth(500);
		column.setResizable(true);
		column.setMoveable(true);
		final ResourceManager resourceManager = new LocalResourceManager(
			JFaceResources.getResources(), sectionsViewer.getControl());
		viewerColumn.setLabelProvider(new ColumnLabelProvider() {

			@Override
			public String getText(Object element) {
				FileSection section = (FileSection) element;
				return section.getSectionName();
			}

			@Override
			public Image getImage(Object element) {
				return resourceManager.createImageWithDefault(CztImages.ZSECTION);
			}

			@Override
			public String getToolTipText(Object element) {
				
				FileSection section = (FileSection) element;
				return "Section " + section.getSectionName() + " (" + section.getFilePath() + ")";
			}
			
		});
		
		// enable tooltips
		ColumnViewerToolTipSupport.enableFor(sectionsViewer);
		
		Table table = sectionsViewer.getTable();
		table.setLayoutData(GridDataFactory.fillDefaults().grab(true, true).create());
//		table.setLinesVisible(true);
		
		sectionsViewer.setContentProvider(new IStructuredContentProvider() {

			@Override
			public Object[] getElements(Object inputElement) {
				if (inputElement instanceof ZEvesSnapshot) {
					return ((ZEvesSnapshot) inputElement).getSections().toArray();
				}
				
				return new Object[0];
			}
			
			@Override
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
			
			@Override
			public void dispose() {}
		});
		
        // add context menu
        final MenuManager mgr = new MenuManager();
        removeSectionAction = new RemoveSectionAction();
        mgr.add(removeSectionAction);
        table.setMenu(mgr.createContextMenu(table));
		
        
        sectionsViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelectionActions();
			}
		});
        updateSelectionActions();
		
		sectionsViewer.setInput(ZEvesCore.getSnapshot());
	}
	
	private void updateSelectionActions() {
		removeSectionAction.setEnabled(!sectionsViewer.getSelection().isEmpty());
	}

	@Override
	public void setFocus() {
		sectionsViewer.getControl().setFocus();
	}
	
	private void initToolBar() {
		IActionBars bars = getViewSite().getActionBars();
		IToolBarManager tm = bars.getToolBarManager();
		tm.add(new ResetAction());
		tm.add(new StopProverAction());
		tm.add(new Separator());
		tm.add(new RefreshAction());
	}

	private void updateState() {
		
		ZEves prover = ZEvesCore.getZEves();
		updateProverState(prover.getApi());
		updateServerState(prover.getServer());
		updateProverDataState(prover.getApi());
		
		reloadSections();
	}
	
	private void reloadSections() {
		sectionsViewer.setInput(sectionsViewer.getInput());
	}

	private void updateProverState(ZEvesApi api) {

		if (api == null) {
			proverStateField.setText("Not available");
			proverAddressField.setText("");
			return;
		}
		
		String connState = api.isConnected() ? "Connected" : "Disconnected";
		proverStateField.setText(connState);
		
		String address = adaptLocalhost(api.getServerAddress()) + ":" + api.getPort();
		proverAddressField.setText(address);
	}
	
	private String adaptLocalhost(String address) {
		if (ZEvesAppLaunch.LOCALHOST_ADDRESS.equals(address)) {
			return "localhost";
		}
		
		return address;
	}
	
	private void updateServerState(ZEvesServer server) {
		
		if (server == null) {
			serverStateField.setText("Not available");
			return;
		}
		
		String serverState = server.isRunning() ? "Running" : "Stopped";
		serverStateField.setText(serverState);
	}
	
	private void fireUpdateState() {
		PlatformUtil.runInUI(new Runnable() {
			@Override
			public void run() {
				updateState();
			}
		});
	}
	
	private void updateProverDataState(final ZEvesApi api) {

		paragraphCountField.setText("");
		
		if (api == null || !api.isConnected()) {
			return;
		}
		
		Job apiQueryJob = new Job("Querying Z/EVES state") {
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				try {
					final int historyLength = api.getHistoryLength();
					
					paragraphCountField.getDisplay().asyncExec(new Runnable() {
						
						@Override
						public void run() {
							paragraphCountField.setText(String.valueOf(historyLength));
						}
					});
				} catch (ZEvesException e) {
					return ZEvesUIPlugin.newErrorStatus(e.getMessage(), e);
				}
				
				return Status.OK_STATUS;
			}
		};
		apiQueryJob.schedule();
	}

	private class RefreshAction extends Action {

		public RefreshAction() {
			super("Refresh");
			setToolTipText("Refresh Prover State");

			// setDescription("?");
			setImageDescriptor(ZEvesImages.REFRESH);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			updateState();
		}
	}
	
	private class ResetAction extends Action {

		public ResetAction() {
			super("Reset");
			setToolTipText("Reset Prover");

			// setDescription("?");
			setImageDescriptor(ZEvesImages.RESET);
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			
			ZEvesCore.getZEves().getExecutor().addCommand(new ZEvesResetCommand() {
				@Override
				protected void completed(IStatus result) {
					fireUpdateState();
				}
			});
		}
	}
	
	private class StopProverAction extends Action {

		public StopProverAction() {
			super("Stop");
			setToolTipText("Stop Prover");

			// setDescription("?");
			setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
					.getImageDescriptor(ISharedImages.IMG_ELCL_STOP));
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			ZEvesUIPlugin.getZEvesProcessSupport().stop();
			fireUpdateState();
		}
	}
	
	private class RemoveSectionAction extends Action {

		public RemoveSectionAction() {
			super("Remove Section");
			setToolTipText("Remove (Undo) Section in Z/EVES Prover");

			// setDescription("?");
			setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
					.getImageDescriptor(ISharedImages.IMG_ELCL_REMOVE));
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {

			ISelection selection = sectionsViewer.getSelection();
			if (selection.isEmpty()) {
				return;
			}
			
			final FileSection selectedSection = 
				(FileSection) ((IStructuredSelection) selection).getFirstElement();
			
			ZEves prover = ZEvesCore.getZEves();
			if (!prover.isRunning()) {
				return;
			}
			
			prover.getExecutor().addCommand(new ZEvesUndoSectionCommand(selectedSection) {
				@Override
				protected void completed(IStatus result) {
					// update the view
					fireUpdateState();
				}
			});
		}
	}
	
}
