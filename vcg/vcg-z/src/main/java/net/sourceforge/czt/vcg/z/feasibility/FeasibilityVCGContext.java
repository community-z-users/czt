package net.sourceforge.czt.vcg.z.feasibility;

import java.util.List;
import java.util.SortedSet;

import net.sourceforge.czt.parser.util.DefinitionTable.Definition;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.vcg.z.AbstractVCGContext;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.ZName;

public class FeasibilityVCGContext extends 
	AbstractVCGContext<SchemaType, SortedSet<Definition>> {

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
