package net.sourceforge.czt.vcg.z.feasibility;

import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;

import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateInfo;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;

public class FeasibilityVCGContext extends 
	AbstractFeasibilityVCGContext<SchemaType, SortedSet<Definition>> {

	private final Map<ZStateInfo, ZName> stateSchemaNames_;
	private final Map<ZStateInfo, AxPara> stateSchemas_;
	private final Map<ZStateInfo, ZNameList> stateGenParams_;

	public FeasibilityVCGContext()
	{
		super();
	}
	@Override
	public ZName getStateName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ZName getInitName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SchemaType getOpType(ZName operationName) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SortedSet<Definition> getOpBindings(ZName operationName) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<? extends InfoTable> getInfoTables() {
		// TODO Auto-generated method stub
		return null;
	}

}
