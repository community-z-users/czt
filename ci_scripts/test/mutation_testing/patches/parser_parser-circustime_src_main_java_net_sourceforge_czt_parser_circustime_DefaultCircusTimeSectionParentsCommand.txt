package net.sourceforge.czt.parser.circustime;

import java.util.Set;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.parser.circus.DefaultCircusSectionParentsCommand;

public class DefaultCircusTimeSectionParentsCommand extends DefaultCircusSectionParentsCommand {
	  
	private boolean isAnyOfCircusTimeStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.CIRCUSTIME.toString()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
		{
			result.add(Section.CIRCUSTIME_TOOLKIT.getName());
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
			// if not the CIRCUSTIME_PRELUDE itself, add it as a default.
			shouldStop = sectName.equals(Section.CIRCUSTIME_PRELUDE.getName()); 
			if (!shouldStop)
			{
				result.add(Section.CIRCUSTIME_PRELUDE.getName());
			}
		}
		return shouldStop || isAnyOfCircusTimeStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.CIRCUSTIME;
	}
}
