package net.sourceforge.czt.util.cli;

import java.util.HashMap;
import java.util.Map;

public class CztToolBuilderDefaultValue {
	
	private Map<String, Boolean> booleanDefaults_ = new HashMap<String, Boolean>();
	
	public Boolean getBooleanDefault(String name)
	{
		return booleanDefaults_.get(name);
	}

	public String getStringDefault(String name)
	{
		return "";//stringDefaults_.get(name);
	}
}
