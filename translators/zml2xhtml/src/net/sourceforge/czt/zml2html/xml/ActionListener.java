package net.sourceforge.czt.zml2html.xml;

/**
 * ActionListener instances produce ActionReport objects
 * based on status information received on its
 * event listening interfaces.
 * 
 * <b>Note:</b> 'Action' in this class documentation
 * is used as a logical term, and does not represent
 * a class or an interface.
 *
 * The interfaces on which status events are received
 * need to be defined by the implementing class.
 * 
 * An action in the <code>ActionListener</code>
 * context is a process with a textual description,
 * a start time and an end time.
 *
 */
public interface ActionListener
{
    /**
     * Set the internal state to prepare for
     * observing an action.
     *
     * <b>Note:</b> This method <i>must</i>
     * be called before the ActionListener
     * instance is registered as a Listener
     * by an Action performing object.
     *
     * @param description Description of the starting Action
     */
    public void startAction(String description);

    /**
     * Signals that the currently running action has stopped.
     */
    public void endAction();

    /**
     * Returns an <code>ActionReport</code> representing
     * the last action that was listened to.
     *
     * @return The <code>ActionReport</code> generated while
     *   listening to the last Action.
     */
    public ActionReport getActionReport();
}

