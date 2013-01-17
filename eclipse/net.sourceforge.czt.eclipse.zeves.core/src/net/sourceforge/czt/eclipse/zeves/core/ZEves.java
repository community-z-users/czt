package net.sourceforge.czt.eclipse.zeves.core;

import java.io.IOException;

import net.sourceforge.czt.eclipse.zeves.core.internal.ZEvesCorePlugin;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesServer;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;


public class ZEves {
	
	private ZEvesServer server;
	private ZEvesApi api;
	private boolean starting = false;
	
	private final ZEvesSnapshot snapshot = new ZEvesSnapshot();
	private final ZEvesLinearExecutor executor = new ZEvesLinearExecutor();
	
	public void stop() {
		
		getExecutor().clear();
		
		if (api != null) {
			try {
				api.disconnect();
			} catch (IOException e) {
				// TODO ignore?
				ZEvesCorePlugin.getDefault().log("Problems disconnecting Z/EVES API: " + e.getMessage(), e);
			}
		}
		
		if (server != null) {
			server.stop();
		}
		
		// finally, execute the reset command
		// the server dies upon disconnection anyway?
//		getExecutor().addCommand(new ZEvesResetCommand());
	}
	
	public boolean isLaunched() {
		return starting || isRunning();
	}

	public boolean isRunning() {
		
		// TODO check server state?
		return api != null && api.isConnected();// && server != null && server.isRunning());
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
	
	public ZEvesLinearExecutor getExecutor() {
		return executor;
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
//				throw new ExecutionException("Unable to connect to Z/EVES server.");
//			}
//		}
//	}
	
}
