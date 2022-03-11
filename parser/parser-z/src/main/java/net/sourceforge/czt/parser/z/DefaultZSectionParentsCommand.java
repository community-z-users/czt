package net.sourceforge.czt.parser.z;

import java.util.Set;
import net.sourceforge.czt.session.DefaultSectionParentsCommand;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.Section;


public class DefaultZSectionParentsCommand extends DefaultSectionParentsCommand {
	  
	/**
	 * Defines whether the given section name is any of the known toolkits as described
	 * by the knownToolkits method of the superclass.
	 * @param sectName
	 * @return
	 */
	private boolean isAnyOfZStandardToolkits(String sectName)
	{
		return knownToolkits(Dialect.Z.toString()).contains(sectName);
	}
	
	/**
	 * Anonymous Z sections have standard_toolkit as its main parent at least. Language extensions
	 * might want to add another set of default parents, hence this method always returns false.
	 */
	@Override
	protected boolean doCalculateDefaultAnonymousParents(Set<String> result)
	{
		// leave just standard toolkit as default (no prelude)
		result.add(Section.STANDARD_TOOLKIT.getName());
		return false;
	}
	
	/**
	 * For named Z sections, the only default parents is the prelude, except the prelude itself, which doesn't have defaults.
	 * For any of the known Standard Z toolkits, the computation should stop, as set_toolkit shouldn't have, say, circus_prelude
	 * as any of its default parents. 
	 */
	@Override
	protected boolean doCalculateDefaultParents(String sectName, Set<String> result) {
		boolean isPrelude = sectName.equals(Section.PRELUDE.getName()); 
		
		// for Z, the only default section is the prelude; except for prelude itself, which doesn't have a parent
		// yet, only add it explicitly if no parent is given to avoid explicit mention of it in XML or pretty-printed files, say.
		if (!isPrelude && result.isEmpty())
		{	
			result.add(Section.PRELUDE.getName());
		}
		
		// we finished the calculation in the case of the section name given is prelude or any of the standard Z toolkit 
		// sections (i.e. don't process default parents for set_toolkit at other lang. extension commands).
		return isPrelude || isAnyOfZStandardToolkits(sectName);
	}

	@Override
	public Dialect getDialect() {
		return Dialect.Z;
	}
}
