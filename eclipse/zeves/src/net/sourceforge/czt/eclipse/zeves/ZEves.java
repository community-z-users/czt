package net.sourceforge.czt.eclipse.zeves;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.eclipse.zeves.editor.ZEvesAnnotations;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ZEvesServer;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;


public class ZEves {
	
	private ZEvesServer server;
	private ZEvesApi api;
	private boolean starting = false;
	
	/**
	 * A mapping from file URI to its Z/Eves state
	 */
	private final Map<IResource, ZEvesFileState> fileStates = new HashMap<IResource, ZEvesFileState>();

	public void stop() {
		
		if (api != null) {
			try {
				api.disconnect();
			} catch (IOException e) {
				// TODO ignore?
				ZEvesPlugin.getDefault().log("Problems disconnecting Z/Eves API: " + e.getMessage(), e);
			}
		}
		
		if (server != null) {
			server.stop();
		}
	}

	public boolean isRunning() {
		
		// TODO check server state?
		return starting || (api != null && api.isConnected());// && server != null && server.isRunning());
	}
	
	public void setApi(ZEvesApi api) {
		this.api = api;
	}
	
	public ZEvesApi getApi() {
		return this.api;
	}
	
	public void setServer(ZEvesServer server) {
		this.server = server;
	}
	
	public ZEvesServer getServer() {
		return this.server;
	}
	
	public void setStarting(boolean starting) {
		this.starting = starting;
	}
	
	public ZEvesFileState getState(IResource resource, boolean create) {
		ZEvesFileState state = fileStates.get(resource);
		if (state == null && create) {
			state = new ZEvesFileState();
			fileStates.put(resource, state);
		}
		
		return state;
	}
	
	public void reset() throws ZEvesException {
		
		// upon reset, reset the API and all the file states
		if (!isRunning()) {
			return;
		}
		
		getApi().reset();

		for (ZEvesFileState state : fileStates.values()) {
			state.clear();
		}

		// also remove all markers
		List<IResource> clearResources = new ArrayList<IResource>(fileStates.keySet());
		clearMarkers(clearResources);
		
		fileStates.clear();
	}

	private void clearMarkers(final List<IResource> clearResources) {
		if (clearResources.isEmpty()) {
			return;
		}
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			public void run(IProgressMonitor monitor) throws CoreException {
				for (IResource resource : clearResources) {
					ZEvesAnnotations.clearMarkers(resource);
				}
			}
		};

		try {
			clearResources.get(0).getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesPlugin.getDefault().log(ce);
		}
	}
	
//	public void start(String serverAddress, int port, ZEvesServer server, IProgressMonitor monitor) {
//		
//		// TODO synchronize to prevent concurrent start?
//		
//		// stop whatever was before
//		stop();
//		
//		this.server = server;
//		this.api = new ZEvesApi(serverAddress, port);
//		
//		if (!server.isRunning()) {
//			server.start();
//		}
//
//		if (!api.isConnected()) {
//			if (!connectRetry(api)) {
//				// cannot connect
//				throw new ExecutionException("Unable to connect to Z/Eves server.");
//			}
//		}
//	}
	
}
