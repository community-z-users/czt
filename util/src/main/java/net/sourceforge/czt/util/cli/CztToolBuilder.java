package net.sourceforge.czt.util.cli;

import java.io.IOException;

public abstract class CztToolBuilder {
	
	public abstract <E extends Throwable> CztTool<E> create();

}

class TypeCheckUtils implements CztTool<IOException> {

	public TypeCheckUtils(TypeCheckUtilsBuilder tcub)
	{
		
	}
	
	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void processArguments(String[] args) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public int run() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String printUsage() {
		// TODO Auto-generated method stub
		return null;
	}
	
}

class TypeCheckUtilsBuilder extends CztToolBuilder {
	
	// If we initialise flags here with default values, and different
    // flags from the default ones are given, the flag control variables
    // won't get changed. Instead use "null" for the case where they
    // are indeed to be set to the default.
    private boolean defaultFlags = true;
    
    private Boolean syntaxOnly = null;
    private Boolean useBeforeDecl = null;
    private Boolean recursiveTypes = null;
    private Boolean printTypes = null;
    private Boolean printZml = null;
    private Boolean printBenchmark = null;
    private Boolean useNameIds = null;
    //private WarningManager.WarningOutput warningOutput = null;
    private String cztpath = null;
    private Boolean printDepsOf = null;
    
	@SuppressWarnings("unchecked")
	public <E extends Throwable> CztTool<E> create()
	{
		return (CztTool<E>)new TypeCheckUtils(this);
	}

	Boolean getSyntaxOnly() {
		return syntaxOnly;
	}

	void setSyntaxOnly(Boolean syntaxOnly) {
		this.syntaxOnly = syntaxOnly;
	}

    Boolean getUseBeforeDecl() {
		return useBeforeDecl;
	}

	void setUseBeforeDecl(Boolean useBeforeDecl) {
		this.useBeforeDecl = useBeforeDecl;
	}

	Boolean getRecursiveTypes() {
		return recursiveTypes;
	}

	void setRecursiveTypes(Boolean recursiveTypes) {
		this.recursiveTypes = recursiveTypes;
	}

	public Boolean getPrintTypes() {
		return printTypes;
	}

	public void setPrintTypes(Boolean printTypes) {
		this.printTypes = printTypes;
	}

	public Boolean getPrintZml() {
		return printZml;
	}

	public void setPrintZml(Boolean printZml) {
		this.printZml = printZml;
	}

	public Boolean getPrintBenchmark() {
		return printBenchmark;
	}

	public void setPrintBenchmark(Boolean printBenchmark) {
		this.printBenchmark = printBenchmark;
	}

	public Boolean getUseNameIds() {
		return useNameIds;
	}

	public void setUseNameIds(Boolean useNameIds) {
		this.useNameIds = useNameIds;
	}

	public String getCztpath() {
		return cztpath;
	}

	public void setCztpath(String cztpath) {
		this.cztpath = cztpath;
	}

	public Boolean getPrintDepsOf() {
		return printDepsOf;
	}

	public void setPrintDepsOf(Boolean printDepsOf) {
		this.printDepsOf = printDepsOf;
	}

	public boolean isDefaultFlags() {
		return defaultFlags;
	}

	public void setDefaultFlags(boolean defaultFlags) {
		this.defaultFlags = defaultFlags;
	}
	
}
