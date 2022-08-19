package net.sourceforge.czt.session;

import java.util.Collections;
import java.util.Set;
import java.util.Map;
import java.util.HashSet;
import java.util.HashMap;

import net.sourceforge.czt.util.Section;

public abstract class DefaultSectionParentsCommand extends AbstractCommand
		implements DefaultSectionParents {

	/** default set of parents from a given section name */
	private Map<String, Set<String>> defaultParents_ = new HashMap<String, Set<String>>();
	
	/**
	 * Delegates calculation of parents for Section.ANONYMOUS sections, collecting the results in the parameter.
	 * @param result set of parents for anonymous section
	 * @return true if calculation is finished; false if should continue.
	 */
	protected abstract boolean doCalculateDefaultAnonymousParents(Set<String> result);

	/**
	 * Delegates calculation of parents for named sections, collecting the results in the parameter.
	 *  As different dialects are often extensions of each other, one might want to stop in between 
	 *  dialects for some cases (i.e. circus dialect handling Z's set_toolkit might not want to add circus_prelude).
	 * @param result set of parents for named section.
	 * @return true if calculation is finished; false if should continue.
	 */
	protected abstract boolean doCalculateDefaultParents(String sectName, Set<String> result);

	/**
	 * Each dialect has a set of known toolkits. By default we use the static information from the Section file.
	 * Extensions might want to change this behaviour. This can be used by extending classes to control whether 
	 * or not to stop calculating default parents. Care needs to be taken in special cases and more complicated
	 * extensions, where the information from util.Section is not enough to determine what are the standard sections
	 * to be considered.
	 * @return set of known toolkits for the current dialect.
	 */
	protected Set<String> knownToolkits()
	{
		return Section.standardSections(getDialect().toString());
	}
	
	protected Set<String> knownToolkits(String dialect)
	{
		return Section.standardSections(dialect);
	}
	
	/**
	 * High level method used by the command computation chain to calculate the default parents of a given section name.
	 * It implements the common features for all extensions and then delegate the actual work to abstract methods.
	 * @param sectName
	 */
	protected void calculateDefaultParents(String sectName)
	{
		assert sectName != null && !sectName.isEmpty();
		
		// calculate if not cached
		if (!defaultParents_.containsKey(sectName))
		{
			Set<String> dp = new HashSet<String>();
			
			// boolean result can be ignored here, but is useful for inheriting classes.
			
			// anonymous sections have more broad parents
			if (sectName.equals(Section.ANONYMOUS.getName()))
			{
				doCalculateDefaultAnonymousParents(dp);
			}
			// named sections might have special sets of parents depending on the dialect
			// (i.e. set_toolkit for circus dialect might not add circus_toolkit to it.
			else
			{
				doCalculateDefaultParents(sectName, dp);
			}
			defaultParents_.put(sectName, dp);
		}
	}

	/**
	 * Computes the calculation for default section parents for the given section name and stores in the section manager.
	 * This result can than be accessed by the defaultParents(String) method.
	 * @throws CommandException whenever the command dialect does not agree with the section manager's.
	 */
	@Override
	protected boolean doCompute(String name, SectionManager manager)
			throws CommandException {
		
		// only calculate default parents for the corresponding section manager dialect?
		// (i.e. Z section manager cannot use a Circus default section parents command).
		if (!manager.getDialect().isExtensionOf(getDialect()))
		{
			throw new CommandException(getDialect(), "Command cannot resolve default section parents for dialect " + getDialect().toString() + 
					". Section manager dialect is " + manager.getDialect());
		}
		
		// calculate the default parents for the given section name.
		// this adds to the underlying map the default parents for the given section name.
		calculateDefaultParents(name);

		// update the manager with the information required.
		manager.endTransaction(new Key<DefaultSectionParents>(name, DefaultSectionParents.class), this);
		return true;
	}
	
	/**
	 * Returns the default set of parents for a given section name for this dialect. Calculations are cached.
	 * If called directly, calculation will take place. Otherwise, the cached results from previous calculation
	 * from the Command computation will be returned.
	 */
	@Override
	public final Set<String> defaultParents(String sectName) {
		// if user decides to call this directly, rather than through a command...?
		calculateDefaultParents(sectName);
		
		// get the result as the default sections for given section name
		Set<String> result = defaultParents_.get(sectName);
				
		// throw a Command exception or just add default?
		//if (!defaultParents_.containsKey(sectName) || result == null)
		//{
		//}		
		assert defaultParents_.containsKey(sectName) && result != null;
		
		return Collections.unmodifiableSet(result);
	}
	
	/**
	 * Dialect of this default parents section calculator command
	 */
	//public abstract Dialect getDialect();	in interface
}
