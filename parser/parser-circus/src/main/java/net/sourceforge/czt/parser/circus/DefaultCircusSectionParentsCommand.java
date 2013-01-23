package net.sourceforge.czt.parser.circus;

import java.util.Set;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.parser.z.DefaultZSectionParentsCommand;

public class DefaultCircusSectionParentsCommand extends DefaultZSectionParentsCommand {
	  
	private boolean isCircusStandardToolkit(String sectName)
	{
		return knownToolkits(Dialect.CIRCUS.dialect()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
		{
			result.add(Section.CIRCUS_PRELUDE.getName());
			result.add(Section.CIRCUS_TOOLKIT.getName());
		}
		return shouldStop;
	}
	
	@Override
	protected boolean doCalculateDefaultParents(String sectName, Set<String> result) {
		boolean shouldStop = super.doCalculateDefaultParents(sectName, result);
		
		if (!shouldStop)
		{
			shouldStop = sectName.equals(Section.CIRCUS_PRELUDE.getName()); 
			if (!shouldStop)
			{
				result.add(Section.CIRCUS_PRELUDE.getName());
			}
		}
		return shouldStop || isCircusStandardToolkit(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.CIRCUS;
	}
}
