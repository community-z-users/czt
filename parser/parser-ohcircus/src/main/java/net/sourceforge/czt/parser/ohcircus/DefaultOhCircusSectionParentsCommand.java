package net.sourceforge.czt.parser.ohcircus;

import java.util.Set;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.parser.circustime.DefaultCircusTimeSectionParentsCommand;

public class DefaultOhCircusSectionParentsCommand extends DefaultCircusTimeSectionParentsCommand {
	  
	private boolean isAnyOfOhCircusStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.OHCIRCUS.toString()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
		{
			result.add(Section.OHCIRCUS_TOOLKIT.getName());
		}
		return shouldStop;
	}
	
	@Override
	protected boolean doCalculateDefaultParents(String sectName, Set<String> result) {
		// calculate the default parents for the given section name for Circus dialect
		boolean shouldStop = super.doCalculateDefaultParents(sectName, result);
		
		// if we should keep calculating defaults go ahead. stop otherwise
		if (!shouldStop)
		{
			// if not the OHCIRCUS_PRELUDE itself, add it as a default.
			shouldStop = sectName.equals(Section.OHCIRCUS_PRELUDE.getName()); 
			if (!shouldStop)
			{
				result.add(Section.OHCIRCUS_PRELUDE.getName());
			}
		}
		return shouldStop || isAnyOfOhCircusStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.OHCIRCUS;
	}
}
