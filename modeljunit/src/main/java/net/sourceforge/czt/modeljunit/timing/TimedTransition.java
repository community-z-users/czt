package net.sourceforge.czt.modeljunit.timing;

import net.sourceforge.czt.modeljunit.Transition;

public class TimedTransition extends Transition {

	protected int time_;
	
	public TimedTransition(int time, Object start, String action, Object end) {
		super(start, action, end);
		time_ = time;
	}
	
	@Override public String toString() {
		return time_ + ":" + super.toString();
	}
	
	/**
	 * Returns the hashscode for a timed transition.
	 * The time that a transition is taken is ignored when 
	 * comparing transitions.
	 */
	@Override public int hashCode() {
		//ignore the time value for hashcodes
		return super.hashCode();
	}
}
