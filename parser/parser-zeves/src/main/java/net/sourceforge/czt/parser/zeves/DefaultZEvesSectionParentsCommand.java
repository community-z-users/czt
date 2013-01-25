package net.sourceforge.czt.parser.zeves;

import java.util.Set;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.parser.z.DefaultZSectionParentsCommand;

public class DefaultZEvesSectionParentsCommand extends DefaultZSectionParentsCommand {
	  
	private boolean isAnyOfZEvesStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.ZEVES.toString()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
		{
			result.add(Section.ZEVES_TOOLKIT.getName());
		}
		return shouldStop;
	}
	
	/**
	 * Takes the Z default parent sections into account and then decides whether to add ZEves prelude to them or not.
	 * If so, adds it and returns whether to continue the calculation of default parents or not.
	 */
	@Override
	protected boolean doCalculateDefaultParents(String sectName, Set<String> result) {
		// calculate the default parents for the given section name for Z dialect
		boolean shouldStop = super.doCalculateDefaultParents(sectName, result);
		
		// if we should keep calculating defaults go ahead. stop otherwise
		if (!shouldStop)
		{
			// if not the ZEVES_PRELUDE itself, add it as a default.
			// this is different from the Z_PRELUDE treatment, which is only
			// added in case of an empty set of parents (i.e. we need the ZEves prelude to account for the language extension)
			shouldStop = sectName.equals(Section.ZEVES_PRELUDE.getName()); 
			if (!shouldStop)
			{
				result.add(Section.ZEVES_PRELUDE.getName());
			}
		}
		// stop when requested by Z dialect, or if found ZEVES_PRELUDE, or if any of the ZEVES Standard toolkits of interest
		return shouldStop || isAnyOfZEvesStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.ZEVES;
	}
}
