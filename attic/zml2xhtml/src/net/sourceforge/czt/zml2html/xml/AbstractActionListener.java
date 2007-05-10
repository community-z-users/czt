package net.sourceforge.czt.zml2html.xml;

/**
 * Basic implementation for all ActionListeners.
 * 
 * This implementation introduces two ActionListener states
 * (<code>ACTION_IN_PROCESS</code> and <code>IDLE</code>)
 * along with code that ensures only one Action
 * can be listened to at a time.
 *
 * A method may throw an IllegalStateException if the ActionListener
 * instance is not in the state required by that method.
 *
 */
public abstract class AbstractActionListener
{
    public static final int ACTION_IN_PROGRESS = 0;
    public static final int IDLE = 1;

    /* instance is either recording an action or not */
    private int state;

    /* The ActionReport being assembled for the current action */
    protected ActionReport curActionReport;

    public AbstractActionListener()
    {
	this.state = IDLE;
    }

    /**
     * Set the internal state to prepare for observing an action.
     *
     * @throws IllegalStateException if the ActionListener
     *   is not in state <code>IDLE</code>.
     */
    public void startAction(String description)
	throws IllegalStateException
    {
	ensureValidState(IDLE);
	state = ACTION_IN_PROGRESS;
    }

    /**
     * Signals that the currently running action has stopped.
     *
     * @throws IllegalStateException if the ActionListener
     *   is not in state <code>ACTION_IN_PROGRESS</code>.
     */
    public void endAction()
	throws IllegalStateException
    {
	ensureValidState(ACTION_IN_PROGRESS);
	state = IDLE;
    }

   /**
    * Retrieves the <code>ActionReport</code> for the most recently
    * recorded action.
    *
    * @returns An ActionReport that encapsulates the status information
    *   produced by the last Action this ActionListener has listened to.
    *
    * @throws IllegalStateException if the ActionListener
    *   is not in state <code>IDLE</code>.
    */
    public ActionReport getActionReport()    
	throws IllegalStateException
    {
	ensureValidState(IDLE);
	return this.curActionReport;
    }

    /**
     * Asserts that the passed state is the current state
     * of the ActionListener instance.
     *
     * @param state The state that is must be current.
     *
     * @throws IllegalStateException if the instance
     *   is not in state <code>state</code>.
     */
    protected void ensureValidState(int state)
	throws IllegalStateException
    {
	if (this.state != state)
	    throw new IllegalStateException("Current state is not '"+state+"'");
    }
}




