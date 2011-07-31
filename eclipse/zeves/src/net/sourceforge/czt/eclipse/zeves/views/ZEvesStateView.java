package net.sourceforge.czt.eclipse.zeves.views;

import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.launch.ZEvesAppLaunch;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ZEvesServer;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;


public class ZEvesStateView extends ViewPart {

	private Label proverStateField;
	private Label proverAddressField;
	
	private Label serverStateField;
	
	private Label paragraphCountField;
	
	@Override
	public void createPartControl(Composite parent) {
		
		Composite main = new Composite(parent, SWT.NONE);
		main.setLayout(GridLayoutFactory.swtDefaults().create());
		
		createProverComponent(main);
		createServerComponent(main);
		
		createProverDataComponent(main);
		
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
		group.setText("Z/Eves prover");
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
		group.setText("Z/Eves executable");
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

	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}
	
	private void initToolBar() {
		IActionBars bars = getViewSite().getActionBars();
		IToolBarManager tm = bars.getToolBarManager();
		tm.add(new AbortAction());
		tm.add(new ResetAction());
		tm.add(new Separator());
		tm.add(new RefreshAction());
	}

	private void updateState() {
		// TODO another thread?
		
		ZEves prover = ZEvesPlugin.getZEves();
		updateProverState(prover.getApi());
		updateServerState(prover.getServer());
		updateProverDataState(prover.getApi());
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
	
	private void updateProverDataState(ZEvesApi api) {

		paragraphCountField.setText("");
		
		if (api == null) {
			return;
		}
		
		try {
			int historyLength = api.getHistoryLength();
			paragraphCountField.setText(String.valueOf(historyLength));
			
			for (int index = 1; index <= historyLength; index++) {
				api.getTheoremNames(index);
			}
			
		} catch (ZEvesException e) {
			ZEvesPlugin.getDefault().log(e.getMessage(), e);
		}
	}

	private class RefreshAction extends Action {

		public RefreshAction() {
			super("Refresh");
			setToolTipText("Refresh Prover State");

			// setDescription("?");
			setImageDescriptor(ZEvesImages.getImageDescriptor(ZEvesImages.IMG_REFRESH));
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
			setImageDescriptor(ZEvesImages.getImageDescriptor(ZEvesImages.IMG_RESET));
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			try {
				ZEvesPlugin.getZEves().reset();
			} catch (ZEvesException e) {
				MessageDialog.openError(paragraphCountField.getShell(), 
						"Problems Resetting Z/Eves", e.getMessage());
				ZEvesPlugin.getDefault().log(e);
			}
		}
	}
	
	private class AbortAction extends Action {

		public AbortAction() {
			super("Abort");
			setToolTipText("Abort Executing Command");

			// setDescription("?");
			setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
					.getImageDescriptor(ISharedImages.IMG_ELCL_STOP));
		}

		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		@Override
		public void run() {
			
			ZEves zeves = ZEvesPlugin.getZEves();
			if (!zeves.isRunning()) {
				return;
			}
			
			zeves.getApi().sendAbort();
		}
	}
	
}
