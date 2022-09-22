package net.sourceforge.czt.parser.circusconf;

import java.util.Set;

import net.sourceforge.czt.parser.circus.DefaultCircusSectionParentsCommand;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;

public class DefaultCircusConfSectionParentsCommand extends DefaultCircusSectionParentsCommand {
	  
	private boolean isAnyOfCircusConfStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.CIRCUSCONF.toString()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
		{
			result.add(Section.CIRCUSCONF_TOOLKIT.getName());
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
			// if not the CIRCUSCONF_PRELUDE itself, add it as a default.
			shouldStop = sectName.equals(Section.CIRCUSCONF_PRELUDE.getName()); 
			if (!shouldStop)
			{
				result.add(Section.CIRCUSCONF_PRELUDE.getName());
			}
		}
		return shouldStop || isAnyOfCircusConfStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.CIRCUSCONF;
	}
}
