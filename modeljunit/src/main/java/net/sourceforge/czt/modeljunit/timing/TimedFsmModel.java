/**
 * 
 */
package net.sourceforge.czt.modeljunit.timing;

import net.sourceforge.czt.modeljunit.FsmModel;

/**
 * @author Scott.
 *	
 * Interface for creating Finite State Machines that using the built
 * in ModelJUnit Timing Framework
 * 
 * @see Timeout
 * @see Time
 *
 */
public interface TimedFsmModel extends FsmModel {

	/**
	 * Function used to get the amount of time to move forward
	 * the next time that the time is incremented. The framework 
	 * will check whether this increment would advance the time
	 * past any enabled timeout(s) and handles execution of the timeout(s).
	 *
	 * @return an integer value greater than zero.
	 */
	public int getNextTimeIncrement();
	
}
