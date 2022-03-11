package net.sourceforge.czt.parser.oz;

import java.util.Set;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.parser.z.DefaultZSectionParentsCommand;

public class DefaultOZSectionParentsCommand extends DefaultZSectionParentsCommand {
	  
	private boolean isAnyOfOZStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.OZ.toString()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
		{
			result.add(Section.OZ_TOOLKIT.getName());
		}
		return shouldStop;
	}
	
	@Override
	protected boolean doCalculateDefaultParents(String sectName, Set<String> result) {
		boolean shouldStop = super.doCalculateDefaultParents(sectName, result);
		
		if (!shouldStop)
		{
			shouldStop = sectName.equals(Section.OZ_TOOLKIT.getName()); 
			if (!shouldStop)
			{
				result.add(Section.OZ_TOOLKIT.getName());
			}
		}
		return shouldStop || isAnyOfOZStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.OZ;
	}
}
