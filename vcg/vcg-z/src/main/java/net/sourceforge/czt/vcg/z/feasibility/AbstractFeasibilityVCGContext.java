package net.sourceforge.czt.vcg.z.feasibility;

import java.util.EnumMap;
import java.util.Map;

import net.sourceforge.czt.vcg.z.AbstractVCGContext;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateInfo;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;

public abstract class AbstractFeasibilityVCGContext<T, B> extends AbstractVCGContext<T, B> {

	private final Map<ZStateInfo, ZName> stateSchemaNames_;
	private final Map<ZStateInfo, AxPara> stateSchemas_;
	private final Map<ZStateInfo, ZNameList> stateGenParams_;

	protected AbstractFeasibilityVCGContext()
	{
		super();
		
		stateSchemaNames_ = new EnumMap<ZStateInfo, ZName>(ZStateInfo.class);
		stateSchemas_ = new EnumMap<ZStateInfo, AxPara>(ZStateInfo.class);
		stateGenParams_ = new EnumMap<ZStateInfo, ZNameList>(ZStateInfo.class);
	}
	
	protected Map<ZStateInfo, ZName> getStateSchemaNames()
	{
		return stateSchemaNames_;
	}
	
	protected Map<ZStateInfo, ZNameList> getStateGenParams()
	{
		return stateGenParams_;
	}

	protected Map<ZStateInfo, AxPara> getStateSchemas()
	{
		return stateSchemas_;
	}
	
	@Override
	public void clear() {
		stateSchemas_.clear();
		stateSchemaNames_.clear();
		stateGenParams_.clear();
		
	}
}
