package net.sourceforge.czt.eclipse.zeves.core;

import java.io.IOException;
import java.util.Set;

import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ZEvesServer;

import org.eclipse.core.runtime.jobs.ISchedulingRule;


public class ZEves implements ISchedulingRule {
	
	private ZEvesServer server;
	private ZEvesApi api;
	private boolean starting = false;
	
	private final ZEvesSnapshot snapshot = new ZEvesSnapshot();
	
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
	
	public ZEvesSnapshot getSnapshot() {
		return snapshot;
	}
	
	public void reset() throws ZEvesException {
		
		// upon reset, reset the API and all the file states
		if (!isRunning()) {
			return;
		}
		
		getApi().reset();
		
		Set<String> clearedPaths = snapshot.clear();

		// also remove all markers
		ResourceUtil.clearMarkers(clearedPaths);
	}

	@Override
	public boolean contains(ISchedulingRule rule) {
		if (rule == this) {
			return true;
		}
		
		return false;
	}

	@Override
	public boolean isConflicting(ISchedulingRule rule) {
		if (rule == this) {
			return true;
		}
		
		return false;
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
