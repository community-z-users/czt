package net.sourceforge.czt.parser.zpatt;

import java.util.Set;

import net.sourceforge.czt.parser.z.DefaultZSectionParentsCommand;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;


public class DefaultZPattSectionParentsCommand extends DefaultZSectionParentsCommand {
	  
	private boolean isAnyOfZPattStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.ZPATT.toString()).contains(sectName);
	}
	
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		boolean shouldStop = super.doCalculateDefaultAnonymousParents(result);
		if (!shouldStop)
			result.add(Section.ORACLE_TOOLKIT.getName());
		return shouldStop;
	}
	
	/**
	 * For named Zpatt sections, we follow the protocol for Z sections as there is no zpatt_prelude. 
	 */
	@Override
	protected boolean doCalculateDefaultParents(String sectName, Set<String> result) {
		boolean shouldStop = super.doCalculateDefaultParents(sectName, result);
		return shouldStop || isAnyOfZPattStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.ZPATT;
	}
}
