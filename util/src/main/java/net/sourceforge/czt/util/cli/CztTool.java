package net.sourceforge.czt.util.cli;

public interface CztTool<E extends Throwable> {
	
	public void reset();
	
	public String printUsage();
	public void processArguments(String[] args);
	
	public int run() throws E;

}
