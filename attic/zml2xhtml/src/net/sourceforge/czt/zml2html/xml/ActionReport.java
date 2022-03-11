package net.sourceforge.czt.zml2html.xml;

import java.util.List;

/**
 * 
 * Records information associated with a logical program action 
 * (e.g., a business logic process).
 * 
 * An <i>Action</i> refers to a process that may produce
 * status information as it executes. Action-performing
 * class can write status or error information to an 
 * <code>ActionReport</code> instance.
 */
public interface ActionReport
{
    /**
     * Returns a short String describing the Action that is being reported.
     *
     * @return A short description of the process that is being reported on.
     */
    public String getDescription(); 

    /**
     * Obtains the list of messages associated with this ActionReport.
     *
     * @return A java.util.List of net.sourceforge.czt.zml2html.ActionMessage instances.
     */
    public List getMessages();

    /**
     * Adds an ActionMessage to the java.util.List of messages.
     *
     * @param message Encapsulation of the message to be added.
     *
     */ 
    public void add(ActionMessage message);
}
